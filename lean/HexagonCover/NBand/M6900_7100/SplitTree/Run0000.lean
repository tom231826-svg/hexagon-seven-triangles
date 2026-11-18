import HexagonCover.NBand.M6900_7100.SplitData
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6900_7100.SplitTree.Run0000
open OwnerTree HexagonCover.NBand.M6900_7100

abbrev Block := Chunk (n := 173) (Certificate := Fin 1199) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def B0068 : Block := .branch 168 ![288230376151712129, 755578637260242745820674, 4384504911992708754611054500510032300402620241924, 5846006723548183536335309995365386419956235657224, 58642753197902479917441407571167582946850313961488, 93536104789177807534223263433152627379965000024096, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 359).pointIds 359), (.leaf 1 (Common.fact 360).pointIds 360), (.leaf 2 (Common.fact 361).pointIds 361), (.leaf 3 (Common.fact 362).pointIds 362), (.leaf 4 (Common.fact 363).pointIds 363), (.leaf 5 (Common.fact 364).pointIds 364), (.leaf 6 (Common.fact 365).pointIds 365)]
theorem treeEq0068 : B0068.tree = HexagonCover.NBand.M6900_7100.SplitData.node0068 := by
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

def B0069 : Block := .branch 168 ![288230376151712129, 755578637260242745820674, 4384504911992708754611054500510032300402620241924, 5846006723548183536335309995365386419956235657224, 11874700803313586534923492924246526317860472586256, 140304157183766700916741178080073684008954841399328, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 359).pointIds 359), (.leaf 1 (Common.fact 360).pointIds 360), (.leaf 2 (Common.fact 361).pointIds 361), (.leaf 3 (Common.fact 362).pointIds 362), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), (.leaf 6 (Common.fact 365).pointIds 365)]
theorem treeEq0069 : B0069.tree = HexagonCover.NBand.M6900_7100.SplitData.node0069 := by
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

def B0067 : Block := .branch 165 ![288230376151712129, 755578637260242745820674, 4384504911992708754611054500510032300402620241924, 5846006723548183536335309995365386419956235657224, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 355).pointIds 355), (.leaf 1 (Common.fact 356).pointIds 356), (.leaf 2 (Common.fact 357).pointIds 357), (.leaf 3 (Common.fact 358).pointIds 358), B0068, B0069, (.leaf 0 [] 0)]
theorem treeEq0067 : B0067.tree = HexagonCover.NBand.M6900_7100.SplitData.node0067 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0068
  · exact treeEq0069
  · rfl

def B0070 : Block := .branch 168 ![288230376151712129, 755578637260242745820674, 4384504911992708754611054500510032300402620241924, 174224571863520570664500254341332505485320, 17720707352637197883219678596684931613328182181904, 93536104789177807534223263433152627379965000024096, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 359).pointIds 359), (.leaf 1 (Common.fact 360).pointIds 360), (.leaf 2 (Common.fact 361).pointIds 361), (.leaf 3 (Common.fact 368).pointIds 368), (.leaf 4 (Common.fact 369).pointIds 369), (.leaf 5 (Common.fact 364).pointIds 364), (.leaf 6 (Common.fact 365).pointIds 365)]
theorem treeEq0070 : B0070.tree = HexagonCover.NBand.M6900_7100.SplitData.node0070 := by
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

def B0066 : Block := .branch 162 ![288230376151712129, 755578637260242745820674, 4384504911992708754611054500510032300402620241924, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 733605341273452737929491223930286829705818013760] ![(.leaf 0 (Common.fact 350).pointIds 350), (.leaf 1 (Common.fact 351).pointIds 351), (.leaf 2 (Common.fact 352).pointIds 352), B0067, B0070, (.leaf 5 (Common.fact 353).pointIds 353), (.leaf 6 (Common.fact 354).pointIds 354)]
theorem treeEq0066 : B0066.tree = HexagonCover.NBand.M6900_7100.SplitData.node0066 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0067
  · exact treeEq0070
  · rfl
  · rfl

def B0071 : Block := .branch 168 ![288230376151712129, 755578637260242745820674, 1461501637330902918203684835077466261090755155972, 2923003448886377699927862958680365044377189376008, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 359).pointIds 359), (.leaf 1 (Common.fact 360).pointIds 360), (.leaf 2 (Common.fact 370).pointIds 370), (.leaf 3 (Common.fact 371).pointIds 371), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 364).pointIds 364), (.leaf 6 (Common.fact 365).pointIds 365)]
theorem treeEq0071 : B0071.tree = HexagonCover.NBand.M6900_7100.SplitData.node0071 := by
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

def B0065 : Block := .branch 161 ![288230376151712129, 755578637260242745820674, 1461501637330902918203684835077466261090755155972, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 733605341273452737929491223930286829705818013760] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), B0066, B0071, (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 349).pointIds 349)]
theorem treeEq0065 : B0065.tree = HexagonCover.NBand.M6900_7100.SplitData.node0065 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0066
  · exact treeEq0071
  · rfl
  · rfl
  · rfl

def B0072 : Block := .branch 168 ![288230376151712129, 755578637260242745820674, 1461501637330902918203684835077466261090755155972, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517163483407775333885838817569259478581312] ![(.leaf 0 (Common.fact 359).pointIds 359), (.leaf 1 (Common.fact 360).pointIds 360), (.leaf 2 (Common.fact 370).pointIds 370), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 364).pointIds 364), (.leaf 6 (Common.fact 373).pointIds 373)]
theorem treeEq0072 : B0072.tree = HexagonCover.NBand.M6900_7100.SplitData.node0072 := by
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

def B0064 : Block := .branch 86 ![288230376151712129, 755578637260242745820674, 1461501637330902918203684835077466261090755155972, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 733605341273452737929491223930286829705818013760] ![(.leaf 0 (Common.fact 340).pointIds 340), (.leaf 1 (Common.fact 341).pointIds 341), (.leaf 2 (Common.fact 342).pointIds 342), B0065, (.leaf 4 (Common.fact 343).pointIds 343), (.leaf 5 (Common.fact 344).pointIds 344), B0072]
theorem treeEq0064 : B0064.tree = HexagonCover.NBand.M6900_7100.SplitData.node0064 := by
  change Tree.branch (86 : Fin 173) _ = Tree.branch (86 : Fin 173) _
  apply congrArg (Tree.branch (86 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0065
  · rfl
  · rfl
  · exact treeEq0072

def B0075 : Block := .branch 168 ![288230376151712129, 755578637260242745820674, 4384504911992708754611054498148849058967797635076, 174224571863678988306263738589820825395208, 17720707352637197883219678596684931613328182181904, 93536104789177807534223263433152627379965000024096, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 359).pointIds 359), (.leaf 1 (Common.fact 360).pointIds 360), (.leaf 2 (Common.fact 376).pointIds 376), (.leaf 3 (Common.fact 377).pointIds 377), (.leaf 4 (Common.fact 369).pointIds 369), (.leaf 5 (Common.fact 364).pointIds 364), (.leaf 6 (Common.fact 365).pointIds 365)]
theorem treeEq0075 : B0075.tree = HexagonCover.NBand.M6900_7100.SplitData.node0075 := by
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

def B0074 : Block := .branch 161 ![288230376151712129, 755578637260242745820674, 1461501637330902918203684832716283019655932549124, 174224571863678988306263738589820825395208, 17720707352637197883219678596684931613328182181904, 93536104789177807534223263433152627379965000024096, 733605341273452737929491223930286829705818013760] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), B0075, (.leaf 3 (Common.fact 375).pointIds 375), (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 349).pointIds 349)]
theorem treeEq0074 : B0074.tree = HexagonCover.NBand.M6900_7100.SplitData.node0074 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0075
  · rfl
  · rfl
  · rfl
  · rfl

def B0073 : Block := .branch 162 ![288230376151712129, 755578637260242745820674, 1461501637330902918203684832716283019655932549124, 174224571863678988306263738589820825395208, 11874700803313586210404939265819799534704452010000, 93536104789177807534223263433152627379965000024096, 733605341273452737929491223930286829705818013760] ![(.leaf 0 (Common.fact 350).pointIds 350), (.leaf 1 (Common.fact 351).pointIds 351), (.leaf 2 (Common.fact 352).pointIds 352), (.leaf 3 (Common.fact 374).pointIds 374), B0074, (.leaf 5 (Common.fact 353).pointIds 353), (.leaf 6 (Common.fact 354).pointIds 354)]
theorem treeEq0073 : B0073.tree = HexagonCover.NBand.M6900_7100.SplitData.node0073 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0074
  · rfl
  · rfl

def B0063 : Block := .branch 71 ![288230376151712129, 755578637260242745820674, 1461501637330902918203684832716283019655932549124, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 733605341273452737929491223930286829705818013760] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), B0064, B0073, (.leaf 4 (Common.fact 338).pointIds 338), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 0 [] 0)]
theorem treeEq0063 : B0063.tree = HexagonCover.NBand.M6900_7100.SplitData.node0063 := by
  change Tree.branch (71 : Fin 173) _ = Tree.branch (71 : Fin 173) _
  apply congrArg (Tree.branch (71 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0064
  · exact treeEq0073
  · rfl
  · rfl
  · rfl

def B0062 : Block := .branch 91 ![288230376151712129, 755578637260242745820674, 1461501637330902918203684832716283019655932549124, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 733605341273452737927015343851716069156019765312] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), (.leaf 3 (Common.fact 333).pointIds 333), (.leaf 4 (Common.fact 334).pointIds 334), (.leaf 5 (Common.fact 335).pointIds 335), B0063]
theorem treeEq0062 : B0062.tree = HexagonCover.NBand.M6900_7100.SplitData.node0062 := by
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
  · exact treeEq0063

def B0061 : Block := .branch 102 ![288230376151712129, 755578637260242745820674, 1461501637330902918203684832716283019655932549124, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 733605341273452732856412942938798463169206943808] ![(.leaf 0 (Common.fact 324).pointIds 324), (.leaf 1 (Common.fact 325).pointIds 325), (.leaf 2 (Common.fact 326).pointIds 326), (.leaf 3 (Common.fact 327).pointIds 327), (.leaf 4 (Common.fact 328).pointIds 328), (.leaf 5 (Common.fact 329).pointIds 329), B0062]
theorem treeEq0061 : B0061.tree = HexagonCover.NBand.M6900_7100.SplitData.node0061 := by
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
  · exact treeEq0062

def B0060 : Block := .branch 108 ![288230376151712129, 755578637260242745820674, 1461501637330902918203684832716283019655932549124, 174224571863678988303902555348386002788360, 11874700803313586210404939265819799534704452010000, 93536104789177807534223263433152627379965000024096, 733605341273463117450130012594055524161865384000] ![(.leaf 0 (Common.fact 318).pointIds 318), (.leaf 1 (Common.fact 319).pointIds 319), (.leaf 2 (Common.fact 320).pointIds 320), (.leaf 3 (Common.fact 321).pointIds 321), B0061, (.leaf 5 (Common.fact 322).pointIds 322), (.leaf 6 (Common.fact 323).pointIds 323)]
theorem treeEq0060 : B0060.tree = HexagonCover.NBand.M6900_7100.SplitData.node0060 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0061
  · rfl
  · rfl

def B0059 : Block := .branch 119 ![288230376151712129, 755578637260242745820674, 1461501637330902918203684832716283019655932549124, 174224571863678988303902555348386002788360, 11874700803313586210404939265819799534704452010000, 93536104789177807534223263433152627379965000024096, 733605341273463117450130012594055524161865384000] ![(.leaf 0 (Common.fact 158).pointIds 158), (.leaf 1 (Common.fact 159).pointIds 159), (.leaf 2 (Common.fact 160).pointIds 160), (.leaf 3 (Common.fact 161).pointIds 161), B0060, (.leaf 5 (Common.fact 163).pointIds 163), (.leaf 6 (Common.fact 317).pointIds 317)]
theorem treeEq0059 : B0059.tree = HexagonCover.NBand.M6900_7100.SplitData.node0059 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0060
  · rfl
  · rfl

def B0058 : Block := .branch 129 ![288230376151712129, 755578637260242745820674, 1461501637330902918203684832716283019655932549124, 174224571863758216466416819685979546738696, 11874700803313586210404939265819799534704452010000, 93536104789177807534223263433152627379965000024096, 733605341273463117450130012594055524161865384000] ![(.leaf 0 (Common.fact 311).pointIds 311), (.leaf 1 (Common.fact 312).pointIds 312), (.leaf 2 (Common.fact 313).pointIds 313), (.leaf 3 (Common.fact 314).pointIds 314), B0059, (.leaf 5 (Common.fact 315).pointIds 315), (.leaf 6 (Common.fact 316).pointIds 316)]
theorem treeEq0058 : B0058.tree = HexagonCover.NBand.M6900_7100.SplitData.node0058 := by
  change Tree.branch (129 : Fin 173) _ = Tree.branch (129 : Fin 173) _
  apply congrArg (Tree.branch (129 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0059
  · rfl
  · rfl

def B0057 : Block := .branch 77 ![288230376151712129, 604462909808414098982402, 1461501637330902918203684832716283019655932549124, 174224571863758216466416819685979546738696, 11874700803313586210404939265819799534704452010000, 93536104789177807534223263433152627379965000024096, 733605341273463117450130012594055524161865384000] ![(.leaf 0 (Common.fact 305).pointIds 305), B0058, (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 308).pointIds 308), (.leaf 5 (Common.fact 309).pointIds 309), (.leaf 6 (Common.fact 310).pointIds 310)]
theorem treeEq0057 : B0057.tree = HexagonCover.NBand.M6900_7100.SplitData.node0057 := by
  change Tree.branch (77 : Fin 173) _ = Tree.branch (77 : Fin 173) _
  apply congrArg (Tree.branch (77 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0058
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0056 : Block := .branch 160 ![288230376151712129, 604462981866008136910338, 6148, 174224571863758216466416819685979546738696, 11874700803313586210404939265819799534704452010000, 93536104789177807534223263433152627379965000024096, 733605341273463117450130012594055524161865384000] ![(.leaf 0 (Common.fact 299).pointIds 299), (.leaf 1 (Common.fact 300).pointIds 300), B0057, (.leaf 3 (Common.fact 301).pointIds 301), (.leaf 4 (Common.fact 302).pointIds 302), (.leaf 5 (Common.fact 303).pointIds 303), (.leaf 6 (Common.fact 304).pointIds 304)]
theorem treeEq0056 : B0056.tree = HexagonCover.NBand.M6900_7100.SplitData.node0056 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0057
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0056 : B0056.accepted = true := by decide +kernel
theorem checked0056 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node0056 (maskNeeds ![288230376151712129, 604462981866008136910338, 6148, 174224571863758216466416819685979546738696, 11874700803313586210404939265819799534704452010000, 93536104789177807534223263433152627379965000024096, 733605341273463117450130012594055524161865384000]) := by
  rw [← treeEq0056]
  exact B0056.sound accepted0056
#print axioms checked0056

def Tip0036_0056 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node0056 ![288230376151712129, 604462981866008136910338, 6148, 174224571863758216466416819685979546738696, 11874700803313586210404939265819799534704452010000, 93536104789177807534223263433152627379965000024096, 733605341273463117450130012594055524161865384000] checked0056
def B0055 : Block := .branch 97 ![288230376151712129, 604462981866008136910338, 6148, 174224571863599760141388291010792458838024, 11874700803313586210404939265819799534704452010000, 93536104789177807534223263433152627379965000024096, 733605341273463117450130012594055524161865384000] ![(.leaf 0 (Common.fact 293).pointIds 293), (.leaf 1 (Common.fact 294).pointIds 294), (.leaf 2 (Common.fact 295).pointIds 295), Tip0036_0056, (.leaf 4 (Common.fact 296).pointIds 296), (.leaf 5 (Common.fact 297).pointIds 297), (.leaf 6 (Common.fact 298).pointIds 298)]
theorem treeEq0055 : B0055.tree = HexagonCover.NBand.M6900_7100.SplitData.node0055 := by
  change Tree.branch (97 : Fin 173) _ = Tree.branch (97 : Fin 173) _
  apply congrArg (Tree.branch (97 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0054 : Block := .branch 107 ![288230376151712129, 604462981866008136910338, 6148, 174224571863599760141388291010792458838024, 11874700803313586210404939265819799534704452010000, 93536104789177807534223263433152627379965000024096, 733605341273463117450130012594055524161865384000] ![(.leaf 0 (Common.fact 287).pointIds 287), (.leaf 1 (Common.fact 288).pointIds 288), (.leaf 2 (Common.fact 289).pointIds 289), B0055, (.leaf 4 (Common.fact 290).pointIds 290), (.leaf 5 (Common.fact 291).pointIds 291), (.leaf 6 (Common.fact 292).pointIds 292)]
theorem treeEq0054 : B0054.tree = HexagonCover.NBand.M6900_7100.SplitData.node0054 := by
  change Tree.branch (107 : Fin 173) _ = Tree.branch (107 : Fin 173) _
  apply congrArg (Tree.branch (107 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0055
  · rfl
  · rfl
  · rfl

def B0053 : Block := .branch 118 ![288230376151712129, 604462981866008136910338, 6148, 174224571863599760141388291010792458838024, 11874700803313586210404939265819799534704452010000, 93536104789177807534223263433152627379965000024096, 733605341294730765382688666560516437126350897216] ![(.leaf 0 (Common.fact 281).pointIds 281), (.leaf 1 (Common.fact 282).pointIds 282), (.leaf 2 (Common.fact 283).pointIds 283), B0054, (.leaf 4 (Common.fact 284).pointIds 284), (.leaf 5 (Common.fact 285).pointIds 285), (.leaf 6 (Common.fact 286).pointIds 286)]
theorem treeEq0053 : B0053.tree = HexagonCover.NBand.M6900_7100.SplitData.node0053 := by
  change Tree.branch (118 : Fin 173) _ = Tree.branch (118 : Fin 173) _
  apply congrArg (Tree.branch (118 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0054
  · rfl
  · rfl
  · rfl

def B0052 : Block := .branch 128 ![288230376151712129, 604462981866008136910338, 6148, 174224571863599760141388291010792458838024, 11874700803313586210404939265819799534704452010000, 93536104789177807534223263433152627379965000024096, 733605341294730765382688666560516437126350897216] ![(.leaf 0 (Common.fact 275).pointIds 275), (.leaf 1 (Common.fact 276).pointIds 276), (.leaf 2 (Common.fact 277).pointIds 277), B0053, (.leaf 4 (Common.fact 278).pointIds 278), (.leaf 5 (Common.fact 279).pointIds 279), (.leaf 6 (Common.fact 280).pointIds 280)]
theorem treeEq0052 : B0052.tree = HexagonCover.NBand.M6900_7100.SplitData.node0052 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0053
  · rfl
  · rfl
  · rfl

def B0051 : Block := .branch 137 ![288230376151712129, 604462981866008136910338, 6148, 79266848140492005727134572552, 11874700803313586210404939265819799534704452010000, 93536104789177807534223263433152627379965000024096, 733605341294730765382688666560516437126350897216] ![(.leaf 0 (Common.fact 270).pointIds 270), (.leaf 1 (Common.fact 271).pointIds 271), (.leaf 2 (Common.fact 272).pointIds 272), B0052, (.leaf 4 (Common.fact 273).pointIds 273), (.leaf 5 (Common.fact 274).pointIds 274), (.leaf 0 [] 0)]
theorem treeEq0051 : B0051.tree = HexagonCover.NBand.M6900_7100.SplitData.node0051 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0052
  · rfl
  · rfl
  · rfl

def B0050 : Block := .branch 151 ![288230376151712129, 604462981866008136910338, 6148, 79266848140492005727134572552, 11874700803313586210404939265819799534704452010000, 93536104789177807534223263433152627379965000024096, 730750845909318845620572094621617446853585403968] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 268).pointIds 268), (.leaf 5 (Common.fact 269).pointIds 269), B0051]
theorem treeEq0050 : B0050.tree = HexagonCover.NBand.M6900_7100.SplitData.node0050 := by
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
  · exact treeEq0051

def B0049 : Block := .branch 163 ![288230376151712129, 604462981866008136910338, 6148, 79266848140492005727134572552, 182687704666362864775460604089535377456991666192, 93536104789177807534223263433152627379965000024096, 730750845909318845620572094621617446853585403968] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), B0050, (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 263).pointIds 263)]
theorem treeEq0049 : B0049.tree = HexagonCover.NBand.M6900_7100.SplitData.node0049 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0050
  · rfl
  · rfl

def B0048 : Block := .branch 113 ![288230376151712129, 604462981866008136910338, 6148, 79266848140492005727134572552, 182687704666362864775460604089535377456991666192, 93536104789177807534223263433152627379965000024096, 730750845909308461026855024966360385860926963776] ![(.leaf 0 (Common.fact 252).pointIds 252), (.leaf 1 (Common.fact 253).pointIds 253), (.leaf 2 (Common.fact 254).pointIds 254), (.leaf 3 (Common.fact 255).pointIds 255), (.leaf 4 (Common.fact 256).pointIds 256), (.leaf 5 (Common.fact 257).pointIds 257), B0049]
theorem treeEq0048 : B0048.tree = HexagonCover.NBand.M6900_7100.SplitData.node0048 := by
  change Tree.branch (113 : Fin 173) _ = Tree.branch (113 : Fin 173) _
  apply congrArg (Tree.branch (113 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0049

def B0047 : Block := .branch 114 ![288230376151712129, 604462981866008136910338, 6148, 79266848140492005727134572552, 182687704666362864775460604089535377456991666192, 93536104789177786765035829293842113257979683143712, 730750845909308461026855024966360385860926963776] ![(.leaf 0 (Common.fact 246).pointIds 246), (.leaf 1 (Common.fact 247).pointIds 247), (.leaf 2 (Common.fact 248).pointIds 248), (.leaf 3 (Common.fact 249).pointIds 249), (.leaf 4 (Common.fact 250).pointIds 250), B0048, (.leaf 6 (Common.fact 251).pointIds 251)]
theorem treeEq0047 : B0047.tree = HexagonCover.NBand.M6900_7100.SplitData.node0047 := by
  change Tree.branch (114 : Fin 173) _ = Tree.branch (114 : Fin 173) _
  apply congrArg (Tree.branch (114 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0048
  · rfl

def B0046 : Block := .branch 124 ![288230376151712129, 604462981866008136910338, 6148, 79266848140492005727134572552, 182687704666362864775460604089535377456991666192, 93536104789177786765035829293842113257979683143712, 730750845888040813094296370999899472896441450560] ![(.leaf 0 (Common.fact 240).pointIds 240), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B0047]
theorem treeEq0046 : B0046.tree = HexagonCover.NBand.M6900_7100.SplitData.node0046 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0047

def B0045 : Block := .branch 78 ![288230376151712129, 604462981866008136910338, 6148, 79266848140492005727134572552, 182687704666362864775460604089535377456991666192, 93536104789177786765035829293842113257979683143712, 730750845888040813094296370999899472896441450560] ![(.leaf 0 (Common.fact 146).pointIds 146), B0046, (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), (.leaf 4 (Common.fact 150).pointIds 150), (.leaf 5 (Common.fact 151).pointIds 151), (.leaf 6 (Common.fact 239).pointIds 239)]
theorem treeEq0045 : B0045.tree = HexagonCover.NBand.M6900_7100.SplitData.node0045 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0046
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0044 : Block := .branch 65 ![288230376151712129, 604462981866008136910338, 6148, 79266848140492005727134572552, 182687704666362864775460604089535377456991666192, 93536104789177786765035829293842113257979683143712, 730750845888040813094296370999899472896441450560] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), B0045, (.leaf 3 (Common.fact 142).pointIds 142), (.leaf 4 (Common.fact 143).pointIds 143), (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 238).pointIds 238)]
theorem treeEq0044 : B0044.tree = HexagonCover.NBand.M6900_7100.SplitData.node0044 := by
  change Tree.branch (65 : Fin 173) _ = Tree.branch (65 : Fin 173) _
  apply congrArg (Tree.branch (65 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0045
  · rfl
  · rfl
  · rfl
  · rfl

def B0043 : Block := .branch 138 ![288230376151712129, 604462981866008136910338, 6148, 79266848140492005727134572552, 182687704666362864775460604089535377456991666192, 93536104789177786765035829293842113257979683143712, 730750845888040813094296370999899472896441450560] ![(.leaf 0 (Common.fact 134).pointIds 134), (.leaf 1 (Common.fact 135).pointIds 135), (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), B0044, (.leaf 5 (Common.fact 138).pointIds 138), (.leaf 6 (Common.fact 237).pointIds 237)]
theorem treeEq0043 : B0043.tree = HexagonCover.NBand.M6900_7100.SplitData.node0043 := by
  change Tree.branch (138 : Fin 173) _ = Tree.branch (138 : Fin 173) _
  apply congrArg (Tree.branch (138 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0044
  · rfl
  · rfl

def B0042 : Block := .branch 139 ![288230376151712129, 604462981866008136910338, 6148, 79266848140492005727134572552, 182687704666362864775460604089535377456991666192, 93536104789177786765035829293842113257979683143712, 730750845888040813094296370999899472896441450560] ![(.leaf 0 (Common.fact 128).pointIds 128), (.leaf 1 (Common.fact 129).pointIds 129), (.leaf 2 (Common.fact 130).pointIds 130), (.leaf 3 (Common.fact 131).pointIds 131), B0043, (.leaf 5 (Common.fact 132).pointIds 132), (.leaf 6 (Common.fact 236).pointIds 236)]
theorem treeEq0042 : B0042.tree = HexagonCover.NBand.M6900_7100.SplitData.node0042 := by
  change Tree.branch (139 : Fin 173) _ = Tree.branch (139 : Fin 173) _
  apply congrArg (Tree.branch (139 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0043
  · rfl
  · rfl

def B0041 : Block := .branch 140 ![288230376151712129, 604462981866008136910338, 6148, 79266848140492005727134572552, 182687704666362864775460604089535377456991666192, 93536104789177786765035829293842113257979683143712, 730750845888040813094296370999899472896441450560] ![(.leaf 0 (Common.fact 122).pointIds 122), (.leaf 1 (Common.fact 123).pointIds 123), (.leaf 2 (Common.fact 124).pointIds 124), (.leaf 3 (Common.fact 125).pointIds 125), B0042, (.leaf 5 (Common.fact 126).pointIds 126), (.leaf 6 (Common.fact 235).pointIds 235)]
theorem treeEq0041 : B0041.tree = HexagonCover.NBand.M6900_7100.SplitData.node0041 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0042
  · rfl
  · rfl

def B0040 : Block := .branch 141 ![288230376151712129, 604462981866008136910338, 6148, 79266848140492005727134572552, 182687704666362864775460604089535377456991666192, 93536104789177786765035829293842113257979683143712, 730750845888040813094296370999899472896441450560] ![(.leaf 0 (Common.fact 116).pointIds 116), (.leaf 1 (Common.fact 117).pointIds 117), (.leaf 2 (Common.fact 118).pointIds 118), (.leaf 3 (Common.fact 119).pointIds 119), B0041, (.leaf 5 (Common.fact 120).pointIds 120), (.leaf 6 (Common.fact 234).pointIds 234)]
theorem treeEq0040 : B0040.tree = HexagonCover.NBand.M6900_7100.SplitData.node0040 := by
  change Tree.branch (141 : Fin 173) _ = Tree.branch (141 : Fin 173) _
  apply congrArg (Tree.branch (141 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0041
  · rfl
  · rfl

def B0039 : Block := .branch 159 ![288230376151712129, 604462981866008136910338, 6148, 79266848140492005727134572552, 182687704666362864775460604089535377456991666192, 93536104789177786765035829293842113257979683143712, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 228).pointIds 228), (.leaf 1 (Common.fact 229).pointIds 229), (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 232).pointIds 232), (.leaf 5 (Common.fact 233).pointIds 233), B0040]
theorem treeEq0039 : B0039.tree = HexagonCover.NBand.M6900_7100.SplitData.node0039 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0040

def B0038 : Block := .branch 79 ![288230376151712129, 72058693549557250, 6148, 79266848140492005727134572552, 182687704666362864775460604089535377456991666192, 93536104789177786765035829293842113257979683143712, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 222).pointIds 222), B0039, (.leaf 2 (Common.fact 223).pointIds 223), (.leaf 3 (Common.fact 224).pointIds 224), (.leaf 4 (Common.fact 225).pointIds 225), (.leaf 5 (Common.fact 226).pointIds 226), (.leaf 6 (Common.fact 227).pointIds 227)]
theorem treeEq0038 : B0038.tree = HexagonCover.NBand.M6900_7100.SplitData.node0038 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0039
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0037 : Block := .branch 132 ![288230376151712129, 72058693549557250, 6148, 79266848140492005727134572552, 184114952359068824656518890058984872593374412816, 93536104789177786765035829293842113257979683143712, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 220).pointIds 220), (.leaf 5 (Common.fact 221).pointIds 221), B0038]
theorem treeEq0037 : B0037.tree = HexagonCover.NBand.M6900_7100.SplitData.node0037 := by
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
  · exact treeEq0038

def B0036 : Block := .branch 133 ![288230376151712129, 72058693549557250, 6148, 79266848140492005727134572552, 184114952359068824656518890058984872593374412816, 93536104789177786765035829293842113257979683143712, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 210).pointIds 210), (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), (.leaf 4 (Common.fact 214).pointIds 214), (.leaf 5 (Common.fact 215).pointIds 215), B0037]
theorem treeEq0036 : B0036.tree = HexagonCover.NBand.M6900_7100.SplitData.node0036 := by
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
  · exact treeEq0037

theorem accepted0036 : B0036.accepted = true := by decide +kernel
theorem checked0036 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node0036 (maskNeeds ![288230376151712129, 72058693549557250, 6148, 79266848140492005727134572552, 184114952359068824656518890058984872593374412816, 93536104789177786765035829293842113257979683143712, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0036]
  exact B0036.sound accepted0036
#print axioms checked0036

def B0111 : Block := .branch 169 ![604463486268066890776961, 1461501637330902918203685134947737924412737848834, 374144419156711147060143317255648683240702699640836, 174224571863520570666861437582767328092168, 52796746648578867920108114581875724085070563213328, 93536104789177807534223263433152627379965000024096, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 426).pointIds 426), (.leaf 1 (Common.fact 427).pointIds 427), (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), (.leaf 4 (Common.fact 430).pointIds 430), (.leaf 5 (Common.fact 431).pointIds 431), (.leaf 6 (Common.fact 432).pointIds 432)]
theorem treeEq0111 : B0111.tree = HexagonCover.NBand.M6900_7100.SplitData.node0111 := by
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

def B0112 : Block := .branch 169 ![604463486268066890776961, 1461501637330902918203685134947737924412737848834, 374144419156711147060143317255648683240702699640836, 174224571863520570666861437582767328092168, 17720707352637197883219678596684931613328182181904, 140304157183766700916741178080073684008954841399328, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 426).pointIds 426), (.leaf 1 (Common.fact 427).pointIds 427), (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), (.leaf 4 (Common.fact 433).pointIds 433), (.leaf 5 (Common.fact 434).pointIds 434), (.leaf 6 (Common.fact 432).pointIds 432)]
theorem treeEq0112 : B0112.tree = HexagonCover.NBand.M6900_7100.SplitData.node0112 := by
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

def B0110 : Block := .branch 165 ![604463486268066890776961, 1461501637330902918203685134947737924412737848834, 374144419156711147060143317255648683240702699640836, 174224571863520570666861437582767328092168, 17720707352637197883219678596684931613328182181904, 93536104789177807534223263433152627379965000024096, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 355).pointIds 355), (.leaf 1 (Common.fact 356).pointIds 356), (.leaf 2 (Common.fact 357).pointIds 357), (.leaf 3 (Common.fact 358).pointIds 358), B0111, B0112, (.leaf 0 [] 0)]
theorem treeEq0110 : B0110.tree = HexagonCover.NBand.M6900_7100.SplitData.node0110 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0111
  · exact treeEq0112
  · rfl

def B0113 : Block := .branch 169 ![604463486268066890776961, 1461501637330902918203685134947737924412737848834, 374144419156711147060143317255648683240702699640836, 174224571863678988306263738589820825395208, 17720707352637197883219678596684931613328182181904, 93536104789177807534223263433152627379965000024096, 2854517163483407775333885838817569259478581312] ![(.leaf 0 (Common.fact 426).pointIds 426), (.leaf 1 (Common.fact 427).pointIds 427), (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 435).pointIds 435), (.leaf 4 (Common.fact 433).pointIds 433), (.leaf 5 (Common.fact 431).pointIds 431), (.leaf 6 (Common.fact 436).pointIds 436)]
theorem treeEq0113 : B0113.tree = HexagonCover.NBand.M6900_7100.SplitData.node0113 := by
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

def B0109 : Block := .branch 86 ![604463486268066890776961, 1461501637330902918203685134947737924412737848834, 374144419156711147060143317255648683240702699640836, 174224571863678988306263738589820825395208, 17720707352637197883219678596684931613328182181904, 93536104789177807534223263433152627379965000024096, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 340).pointIds 340), (.leaf 1 (Common.fact 341).pointIds 341), (.leaf 2 (Common.fact 342).pointIds 342), B0110, (.leaf 4 (Common.fact 343).pointIds 343), (.leaf 5 (Common.fact 344).pointIds 344), B0113]
theorem treeEq0109 : B0109.tree = HexagonCover.NBand.M6900_7100.SplitData.node0109 := by
  change Tree.branch (86 : Fin 173) _ = Tree.branch (86 : Fin 173) _
  apply congrArg (Tree.branch (86 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0110
  · rfl
  · rfl
  · exact treeEq0113

def B0114 : Block := .branch 169 ![604463486268066890776961, 1461501637330902918203685134947737924412737848834, 374144419156711147060143317250926316757833054427140, 174224571863678988310986105072690470608904, 17720707352637197883219678596684931613328182181904, 93536104789177807534223263433152627379965000024096, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 426).pointIds 426), (.leaf 1 (Common.fact 427).pointIds 427), (.leaf 2 (Common.fact 437).pointIds 437), (.leaf 3 (Common.fact 438).pointIds 438), (.leaf 4 (Common.fact 433).pointIds 433), (.leaf 5 (Common.fact 431).pointIds 431), (.leaf 6 (Common.fact 432).pointIds 432)]
theorem treeEq0114 : B0114.tree = HexagonCover.NBand.M6900_7100.SplitData.node0114 := by
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

def B0108 : Block := .branch 72 ![604463486268066890776961, 1461501637330902918203685134947737924412737848834, 374144419156711147060143317250926316757833054427140, 174224571863678988306263738589820825395208, 17720707352637197883219678596684931613328182181904, 93536104789177807534223263433152627379965000024096, 2854517163483408092633392158151600969560358976] ![(.leaf 0 (Common.fact 421).pointIds 421), (.leaf 1 (Common.fact 422).pointIds 422), B0109, B0114, (.leaf 4 (Common.fact 423).pointIds 423), (.leaf 5 (Common.fact 424).pointIds 424), (.leaf 6 (Common.fact 425).pointIds 425)]
theorem treeEq0108 : B0108.tree = HexagonCover.NBand.M6900_7100.SplitData.node0108 := by
  change Tree.branch (72 : Fin 173) _ = Tree.branch (72 : Fin 173) _
  apply congrArg (Tree.branch (72 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0109
  · exact treeEq0114
  · rfl
  · rfl
  · rfl

def B0107 : Block := .branch 91 ![604463486268066890776961, 1461501637330902918203685134947737924412737848834, 374144419156711147060143317250926316757833054427140, 174224571863678988306263738589820825395208, 17720707352637197883219678596684931613328182181904, 93536104789177807534223263433152627379965000024096, 2854517163483408090157512079580840419762110528] ![(.leaf 0 (Common.fact 420).pointIds 420), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), (.leaf 3 (Common.fact 333).pointIds 333), (.leaf 4 (Common.fact 334).pointIds 334), (.leaf 5 (Common.fact 335).pointIds 335), B0108]
theorem treeEq0107 : B0107.tree = HexagonCover.NBand.M6900_7100.SplitData.node0107 := by
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
  · exact treeEq0108

def B0106 : Block := .branch 102 ![604463486268066890776961, 1461501637330902918203685134947737924412737848834, 374144419156711147060143317250926316757833054427140, 174224571863678988306263738589820825395208, 17720707352637197883219678596684931613328182181904, 93536104789177807534223263433152627379965000024096, 2854517163483403019555111166663234432949289024] ![(.leaf 0 (Common.fact 419).pointIds 419), (.leaf 1 (Common.fact 325).pointIds 325), (.leaf 2 (Common.fact 326).pointIds 326), (.leaf 3 (Common.fact 327).pointIds 327), (.leaf 4 (Common.fact 328).pointIds 328), (.leaf 5 (Common.fact 329).pointIds 329), B0107]
theorem treeEq0106 : B0106.tree = HexagonCover.NBand.M6900_7100.SplitData.node0106 := by
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
  · exact treeEq0107

def B0105 : Block := .branch 76 ![604463486268066890776961, 1461501637330902918203685134947737924412737848834, 374144419156711147060143317175368453031918731008004, 174224571863678988306263738589820825395208, 17720707352637197883219678596684931613328182181904, 93536104789177807534223263433152627379965000024096, 2854522608011658348287596235914014333899112512] ![(.leaf 0 (Common.fact 413).pointIds 413), (.leaf 1 (Common.fact 414).pointIds 414), B0106, (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 418).pointIds 418)]
theorem treeEq0105 : B0105.tree = HexagonCover.NBand.M6900_7100.SplitData.node0105 := by
  change Tree.branch (76 : Fin 173) _ = Tree.branch (76 : Fin 173) _
  apply congrArg (Tree.branch (76 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0106
  · rfl
  · rfl
  · rfl
  · rfl

def B0104 : Block := .branch 97 ![604463486268066890776961, 1461501637330902918203685134947737924412737848834, 374144419156711147060143317175368453031918731008004, 174224571863520531981235209914633737494536, 17720707352637197883219678596684931613328182181904, 93536104789177807534223263433152627379965000024096, 2854522629279306280846250202374927298384625728] ![(.leaf 0 (Common.fact 293).pointIds 293), (.leaf 1 (Common.fact 294).pointIds 294), (.leaf 2 (Common.fact 295).pointIds 295), B0105, (.leaf 4 (Common.fact 296).pointIds 296), (.leaf 5 (Common.fact 297).pointIds 297), (.leaf 6 (Common.fact 412).pointIds 412)]
theorem treeEq0104 : B0104.tree = HexagonCover.NBand.M6900_7100.SplitData.node0104 := by
  change Tree.branch (97 : Fin 173) _ = Tree.branch (97 : Fin 173) _
  apply congrArg (Tree.branch (97 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0105
  · rfl
  · rfl
  · rfl

def B0103 : Block := .branch 107 ![604463486268066890776961, 1461501637330902918203685134947737924412737848834, 374144419156711147060143317175368453031918731008004, 174224571863520531981235209914633737494536, 17720707352637197883219678596684931613328182181904, 93536104789177807534223263433152627379965000024096, 2854522629279306280846250202374927298384625728] ![(.leaf 0 (Common.fact 287).pointIds 287), (.leaf 1 (Common.fact 288).pointIds 288), (.leaf 2 (Common.fact 289).pointIds 289), B0104, (.leaf 4 (Common.fact 290).pointIds 290), (.leaf 5 (Common.fact 291).pointIds 291), (.leaf 6 (Common.fact 411).pointIds 411)]
theorem treeEq0103 : B0103.tree = HexagonCover.NBand.M6900_7100.SplitData.node0103 := by
  change Tree.branch (107 : Fin 173) _ = Tree.branch (107 : Fin 173) _
  apply congrArg (Tree.branch (107 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0104
  · rfl
  · rfl
  · rfl

def B0102 : Block := .branch 118 ![604463486268066890776961, 1461501637330902918203685134947737924412737848834, 374144419156711147060143317175368453031918731008004, 174224571863520531981235209914633737494536, 17720707352637197883219678596684931613328182181904, 93536104789177807534223263433152627379965000024096, 2854522629279306280846250202374927298384625728] ![(.leaf 0 (Common.fact 281).pointIds 281), (.leaf 1 (Common.fact 282).pointIds 282), (.leaf 2 (Common.fact 283).pointIds 283), B0103, (.leaf 4 (Common.fact 284).pointIds 284), (.leaf 5 (Common.fact 285).pointIds 285), (.leaf 6 (Common.fact 410).pointIds 410)]
theorem treeEq0102 : B0102.tree = HexagonCover.NBand.M6900_7100.SplitData.node0102 := by
  change Tree.branch (118 : Fin 173) _ = Tree.branch (118 : Fin 173) _
  apply congrArg (Tree.branch (118 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0103
  · rfl
  · rfl
  · rfl

def B0101 : Block := .branch 128 ![604463486268066890776961, 1461501637330902918203685134947737924412737848834, 374144419156711147060143317175368453031918731008004, 174224571863520531981235209914633737494536, 17720707352637197883219678596684931613328182181904, 93536104789177807534223263433152627379965000024096, 2854522629279306280846250202374927298384625728] ![(.leaf 0 (Common.fact 275).pointIds 275), (.leaf 1 (Common.fact 276).pointIds 276), (.leaf 2 (Common.fact 277).pointIds 277), B0102, (.leaf 4 (Common.fact 278).pointIds 278), (.leaf 5 (Common.fact 279).pointIds 279), (.leaf 6 (Common.fact 409).pointIds 409)]
theorem treeEq0101 : B0101.tree = HexagonCover.NBand.M6900_7100.SplitData.node0101 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0102
  · rfl
  · rfl
  · rfl

def B0100 : Block := .branch 162 ![604463486268066890776961, 1461501637330902918203685134947737924412737848834, 374144419156711147060143317175368453031918731008004, 174224571863520531981235209914633737494536, 11874700803313586210404939265819799534704452010000, 93536104789177807534223263433152627379965000024096, 2854522629279306280846250202374927298384625728] ![(.leaf 0 (Common.fact 350).pointIds 350), (.leaf 1 (Common.fact 351).pointIds 351), (.leaf 2 (Common.fact 352).pointIds 352), (.leaf 3 (Common.fact 407).pointIds 407), B0101, (.leaf 5 (Common.fact 353).pointIds 353), (.leaf 6 (Common.fact 408).pointIds 408)]
theorem treeEq0100 : B0100.tree = HexagonCover.NBand.M6900_7100.SplitData.node0100 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0101
  · rfl
  · rfl

def B0099 : Block := .branch 137 ![604463486268066890776961, 1461501637330902918203685134947737924412737848834, 374144419156711147060143317175368453031918731008004, 38687987410909568413229064, 11874700803313586210404939265819799534704452010000, 93536104789177807534223263433152627379965000024096, 2854522629279306280846250202374927298384625728] ![(.leaf 0 (Common.fact 270).pointIds 270), (.leaf 1 (Common.fact 271).pointIds 271), (.leaf 2 (Common.fact 272).pointIds 272), B0100, (.leaf 4 (Common.fact 273).pointIds 273), (.leaf 5 (Common.fact 274).pointIds 274), (.leaf 0 [] 0)]
theorem treeEq0099 : B0099.tree = HexagonCover.NBand.M6900_7100.SplitData.node0099 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0100
  · rfl
  · rfl
  · rfl

def B0098 : Block := .branch 151 ![604463486268066890776961, 1461501637330902918203685134947737924412737848834, 374144419156711147060143317175368453031918731008004, 38687987410909568413229064, 11874700803313586210404939265819799534704452010000, 93536104789177807534223263433152627379965000024096, 27243867386518729678263475937025619132480] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 268).pointIds 268), (.leaf 5 (Common.fact 269).pointIds 269), B0099]
theorem treeEq0098 : B0098.tree = HexagonCover.NBand.M6900_7100.SplitData.node0098 := by
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
  · exact treeEq0099

def B0097 : Block := .branch 163 ![604463486268066890776961, 1461501637330902918203685134947737924412737848834, 374144419156711147060143317175368453031918731008004, 38687987410909568413229064, 182687704666362864775460604089535377456991666192, 93536104789177807534223263433152627379965000024096, 27243867386518729678263475937025619132480] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), B0098, (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 263).pointIds 263)]
theorem treeEq0097 : B0097.tree = HexagonCover.NBand.M6900_7100.SplitData.node0097 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0098
  · rfl
  · rfl

def B0096 : Block := .branch 71 ![604463486268066890776961, 1461501637330902918203685134947737924412737848834, 374144419156711147060143317175405346520066150111236, 38685626227668133590622216, 182687704666362864775460604089535377456991666192, 93536104789177807534223263433152627379965000024096, 27243867386518729678263475937025619132480] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 406).pointIds 406), B0097, (.leaf 4 (Common.fact 338).pointIds 338), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 0 [] 0)]
theorem treeEq0096 : B0096.tree = HexagonCover.NBand.M6900_7100.SplitData.node0096 := by
  change Tree.branch (71 : Fin 173) _ = Tree.branch (71 : Fin 173) _
  apply congrArg (Tree.branch (71 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0097
  · rfl
  · rfl
  · rfl

def B0095 : Block := .branch 114 ![604463486268066890776961, 1461501637330902918203685134947737924412737848834, 374144419156711147060143317175405346520066150111236, 38685626227668133590622216, 182687704666362864775460604089535377456991666192, 93536104789177786765035829293842113257979683143712, 27243867386518729678263475937025619132480] ![(.leaf 0 (Common.fact 405).pointIds 405), (.leaf 1 (Common.fact 247).pointIds 247), (.leaf 2 (Common.fact 248).pointIds 248), (.leaf 3 (Common.fact 249).pointIds 249), (.leaf 4 (Common.fact 250).pointIds 250), B0096, (.leaf 6 (Common.fact 251).pointIds 251)]
theorem treeEq0095 : B0095.tree = HexagonCover.NBand.M6900_7100.SplitData.node0095 := by
  change Tree.branch (114 : Fin 173) _ = Tree.branch (114 : Fin 173) _
  apply congrArg (Tree.branch (114 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0096
  · rfl

theorem accepted0095 : B0095.accepted = true := by decide +kernel
theorem checked0095 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node0095 (maskNeeds ![604463486268066890776961, 1461501637330902918203685134947737924412737848834, 374144419156711147060143317175405346520066150111236, 38685626227668133590622216, 182687704666362864775460604089535377456991666192, 93536104789177786765035829293842113257979683143712, 27243867386518729678263475937025619132480]) := by
  rw [← treeEq0095]
  exact B0095.sound accepted0095
#print axioms checked0095

def B0173 : Block := .branch 170 ![94266855607843243416434530245027883298303978242433, 1461501637330902918204303802735925710892893734402, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 182699203488105857128017958444269711768393187344, 233840261972987002208454690542538204970878178295840, 374144419179191050924858278645432370053532760932416] ![(.leaf 0 (Common.fact 543).pointIds 543), (.leaf 1 (Common.fact 544).pointIds 544), (.leaf 2 (Common.fact 545).pointIds 545), (.leaf 3 (Common.fact 546).pointIds 546), (.leaf 4 (Common.fact 547).pointIds 547), (.leaf 5 (Common.fact 548).pointIds 548), (.leaf 6 (Common.fact 549).pointIds 549)]
theorem treeEq0173 : B0173.tree = HexagonCover.NBand.M6900_7100.SplitData.node0173 := by
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

def B0174 : Block := .branch 170 ![94266855607843243416434530245027883298303978242433, 618970019642691236961191426, 4384504911992708754611054500510032300402620241924, 5846006723548183536335309995365386419956235657224, 182699203488105857128017958444269711768393187344, 233840261972987002208454690542538204970878178295840, 374144419179191050924858278645432370053532760932416] ![(.leaf 0 (Common.fact 543).pointIds 543), (.leaf 1 (Common.fact 550).pointIds 550), (.leaf 2 (Common.fact 551).pointIds 551), (.leaf 3 (Common.fact 546).pointIds 546), (.leaf 4 (Common.fact 547).pointIds 547), (.leaf 5 (Common.fact 548).pointIds 548), (.leaf 6 (Common.fact 549).pointIds 549)]
theorem treeEq0174 : B0174.tree = HexagonCover.NBand.M6900_7100.SplitData.node0174 := by
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

def B0175 : Block := .branch 170 ![94266855607843243416434530245027883298303978242433, 618970019642691236961191426, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 182699203488105857128017958444269711768393187344, 233840261972987002208454690542538204970878178295840, 375605920816521953843061653993138831728119968694336] ![(.leaf 0 (Common.fact 543).pointIds 543), (.leaf 1 (Common.fact 550).pointIds 550), (.leaf 2 (Common.fact 545).pointIds 545), (.leaf 3 (Common.fact 546).pointIds 546), (.leaf 4 (Common.fact 547).pointIds 547), (.leaf 5 (Common.fact 548).pointIds 548), (.leaf 6 (Common.fact 552).pointIds 552)]
theorem treeEq0175 : B0175.tree = HexagonCover.NBand.M6900_7100.SplitData.node0175 := by
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

def B0172 : Block := .branch 160 ![94266855607843243416434530245027883298303978242433, 618970019642691236961191426, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 182699203488105857128017958444269711768393187344, 233840261972987002208454690542538204970878178295840, 374144419179191050924858278645432370053532760932416] ![(.leaf 0 (Common.fact 299).pointIds 299), B0173, B0174, (.leaf 3 (Common.fact 301).pointIds 301), (.leaf 4 (Common.fact 302).pointIds 302), (.leaf 5 (Common.fact 303).pointIds 303), B0175]
theorem treeEq0172 : B0172.tree = HexagonCover.NBand.M6900_7100.SplitData.node0172 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0173
  · exact treeEq0174
  · rfl
  · rfl
  · rfl
  · exact treeEq0175

def B0176 : Block := .branch 170 ![93536104789177791958600338428897971189972715176321, 730750818665451459101842416358141510927477900802, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 182699203488105857128017958444269711768393187344, 233840261972987002208454690542538204970878178295840, 374144419179191050924858278645432370053532760932416] ![(.leaf 0 (Common.fact 553).pointIds 553), (.leaf 1 (Common.fact 554).pointIds 554), (.leaf 2 (Common.fact 545).pointIds 545), (.leaf 3 (Common.fact 546).pointIds 546), (.leaf 4 (Common.fact 547).pointIds 547), (.leaf 5 (Common.fact 548).pointIds 548), (.leaf 6 (Common.fact 549).pointIds 549)]
theorem treeEq0176 : B0176.tree = HexagonCover.NBand.M6900_7100.SplitData.node0176 := by
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

def B0177 : Block := .branch 170 ![93536104789177791958600338428897971189972715176321, 618970019642691236961191426, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 182699203488105857128017958444269711768393187344, 233840261972987002208454690542538204970878178295840, 374875169997856502383960121061790511563360727203904] ![(.leaf 0 (Common.fact 553).pointIds 553), (.leaf 1 (Common.fact 550).pointIds 550), (.leaf 2 (Common.fact 545).pointIds 545), (.leaf 3 (Common.fact 546).pointIds 546), (.leaf 4 (Common.fact 547).pointIds 547), (.leaf 5 (Common.fact 548).pointIds 548), (.leaf 6 (Common.fact 555).pointIds 555)]
theorem treeEq0177 : B0177.tree = HexagonCover.NBand.M6900_7100.SplitData.node0177 := by
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

def B0171 : Block := .branch 159 ![93536104789177791958600338428897971189972715176321, 618970019642691236961191426, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 182699203488105857128017958444269711768393187344, 233840261972987002208454690542538204970878178295840, 374144419179191050924858278645432370053532760932416] ![B0172, B0176, (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 232).pointIds 232), (.leaf 5 (Common.fact 233).pointIds 233), B0177]
theorem treeEq0171 : B0171.tree = HexagonCover.NBand.M6900_7100.SplitData.node0171 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0172
  · exact treeEq0176
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0177

def B0178 : Block := .branch 170 ![93536104789177791957333925768709027168750911095169, 1267650600228229402596214834690, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 182699203488105857128017958444269711768393187344, 233840261972987002208454690542538204970878178295840, 374144419179191050924858278645432370053532760932416] ![(.leaf 0 (Common.fact 556).pointIds 556), (.leaf 1 (Common.fact 557).pointIds 557), (.leaf 2 (Common.fact 545).pointIds 545), (.leaf 3 (Common.fact 546).pointIds 546), (.leaf 4 (Common.fact 547).pointIds 547), (.leaf 5 (Common.fact 548).pointIds 548), (.leaf 6 (Common.fact 549).pointIds 549)]
theorem treeEq0178 : B0178.tree = HexagonCover.NBand.M6900_7100.SplitData.node0178 := by
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

def B0179 : Block := .branch 170 ![93536104789177791957333925768709027168750911095169, 618970019642691236961191426, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 182699203488105857128017958444269711768393187344, 233840261972987002208454690542538204970878178295840, 374144419179191050926125929245660599455029464137792] ![(.leaf 0 (Common.fact 556).pointIds 556), (.leaf 1 (Common.fact 550).pointIds 550), (.leaf 2 (Common.fact 545).pointIds 545), (.leaf 3 (Common.fact 546).pointIds 546), (.leaf 4 (Common.fact 547).pointIds 547), (.leaf 5 (Common.fact 548).pointIds 548), (.leaf 6 (Common.fact 558).pointIds 558)]
theorem treeEq0179 : B0179.tree = HexagonCover.NBand.M6900_7100.SplitData.node0179 := by
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

def B0170 : Block := .branch 100 ![93536104789177791957333925768709027168750911095169, 618970019642691236961191426, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 182699203488105857128017958444269711768393187344, 233840261972987002208454690542538204970878178295840, 374144419179191050924858278645432370053532760932416] ![B0171, B0178, (.leaf 2 (Common.fact 539).pointIds 539), (.leaf 3 (Common.fact 540).pointIds 540), (.leaf 4 (Common.fact 541).pointIds 541), (.leaf 5 (Common.fact 542).pointIds 542), B0179]
theorem treeEq0170 : B0170.tree = HexagonCover.NBand.M6900_7100.SplitData.node0170 := by
  change Tree.branch (100 : Fin 173) _ = Tree.branch (100 : Fin 173) _
  apply congrArg (Tree.branch (100 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0171
  · exact treeEq0178
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0179

def B0180 : Block := .branch 170 ![5192298096474866913910771228344705, 618970019642691236961191426, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 182699203488105857128017958444269711768393187344, 327376366762122253677625402528447396402928890019872, 374144419179191050924858278645432370053532760932416] ![(.leaf 0 (Common.fact 559).pointIds 559), (.leaf 1 (Common.fact 550).pointIds 550), (.leaf 2 (Common.fact 545).pointIds 545), (.leaf 3 (Common.fact 546).pointIds 546), (.leaf 4 (Common.fact 547).pointIds 547), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 549).pointIds 549)]
theorem treeEq0180 : B0180.tree = HexagonCover.NBand.M6900_7100.SplitData.node0180 := by
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

def B0169 : Block := .branch 166 ![5192298096474866913910771228344705, 618970019642691236961191426, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 182699203488105857128017958444269711768393187344, 233840261972987002208454690542538204970878178295840, 374144419179191050925175191295489427403906936733760] ![B0170, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), B0180, (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq0169 : B0169.tree = HexagonCover.NBand.M6900_7100.SplitData.node0169 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0170
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0180
  · rfl

def B0181 : Block := .branch 170 ![5192298096474866913910771228344705, 618970019642691236961191426, 77919046967349146032132, 8769009998209989372742602289545497123000919547912, 182699203488105857128017958444269711768393187344, 233840261972987002208454690542538204970878178295840, 374144419179191050924858278645432370053532760932416] ![(.leaf 0 (Common.fact 559).pointIds 559), (.leaf 1 (Common.fact 550).pointIds 550), (.leaf 2 (Common.fact 561).pointIds 561), (.leaf 3 (Common.fact 562).pointIds 562), (.leaf 4 (Common.fact 547).pointIds 547), (.leaf 5 (Common.fact 548).pointIds 548), (.leaf 6 (Common.fact 549).pointIds 549)]
theorem treeEq0181 : B0181.tree = HexagonCover.NBand.M6900_7100.SplitData.node0181 := by
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

def B0168 : Block := .branch 161 ![5192298096474866913910771228344705, 618970019642691236961191426, 77919046967349146032132, 5846006723548183536335309995365386419956235657224, 182699203488105857128017958444269711768393187344, 233840261972987002208454690542538204970878178295840, 374144419179191051249693744953916154187062957310016] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), B0169, B0181, (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 538).pointIds 538)]
theorem treeEq0168 : B0168.tree = HexagonCover.NBand.M6900_7100.SplitData.node0168 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0169
  · exact treeEq0181
  · rfl
  · rfl
  · rfl

def B0183 : Block := .branch 170 ![93536104789177791957333925768709027168750911095169, 618970019642691236961191426, 77919046967349146032132, 5846006723548183536335309995365386419956235657224, 2865994207154912114673926293633324584167112720, 182687704708898160640577912022457203385962987552, 374144419179191050924858278645432370053532760932416] ![(.leaf 0 (Common.fact 556).pointIds 556), (.leaf 1 (Common.fact 550).pointIds 550), (.leaf 2 (Common.fact 561).pointIds 561), (.leaf 3 (Common.fact 546).pointIds 546), (.leaf 4 (Common.fact 564).pointIds 564), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 549).pointIds 549)]
theorem treeEq0183 : B0183.tree = HexagonCover.NBand.M6900_7100.SplitData.node0183 := by
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

def B0182 : Block := .branch 166 ![5192298096474866913910771228344705, 618970019642691236961191426, 77919046967349146032132, 5846006723548183536335309995365386419956235657224, 2865994207154912114673926293633324584167112720, 182687704708898160640577912022457203385962987552, 374144419179191050925175191295489427403906936733760] ![B0183, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 563).pointIds 563), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq0182 : B0182.tree = HexagonCover.NBand.M6900_7100.SplitData.node0182 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0183
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0167 : Block := .branch 157 ![5192298096474866913910771228344705, 618970019642691236961191426, 77919046967349146032132, 5846006723548183536335309995365386419956235657224, 2865994207154912114673926293633324584167112720, 233840261972987002208454690542538204970878178295840, 374144419179191051249693744953916154187062957310016] ![(.leaf 0 (Common.fact 205).pointIds 205), (.leaf 1 (Common.fact 206).pointIds 206), (.leaf 2 (Common.fact 207).pointIds 207), (.leaf 3 (Common.fact 208).pointIds 208), B0168, B0182, (.leaf 0 [] 0)]
theorem treeEq0167 : B0167.tree = HexagonCover.NBand.M6900_7100.SplitData.node0167 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0168
  · exact treeEq0182
  · rfl

def B0185 : Block := .branch 170 ![93536104789177791957333925768709027168750911095169, 618970019642691236961191426, 77919046967349146032132, 5846006723548183536335309995365386419956235657224, 11498821742992352557354354734334311401619472, 233843116468372414128216807114477103961150943789088, 374144419179191050924858278645432370053532760932416] ![(.leaf 0 (Common.fact 556).pointIds 556), (.leaf 1 (Common.fact 550).pointIds 550), (.leaf 2 (Common.fact 561).pointIds 561), (.leaf 3 (Common.fact 546).pointIds 546), (.leaf 4 (Common.fact 567).pointIds 567), (.leaf 5 (Common.fact 568).pointIds 568), (.leaf 6 (Common.fact 549).pointIds 549)]
theorem treeEq0185 : B0185.tree = HexagonCover.NBand.M6900_7100.SplitData.node0185 := by
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

def B0184 : Block := .branch 166 ![5192298096474866913910771228344705, 618970019642691236961191426, 77919046967349146032132, 5846006723548183536335309995365386419956235657224, 11498821742992352557354354734334311401619472, 233843116468372414128216807114477103961150943789088, 374144419179191050925175191295489427403906936733760] ![B0185, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq0184 : B0184.tree = HexagonCover.NBand.M6900_7100.SplitData.node0184 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0185
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0166 : Block := .branch 151 ![5192298096474866913910771228344705, 618970019642691236961191426, 77919046967349146032132, 5846006723548183536335309995365386419956235657224, 11498821742992352557354354734334311401619472, 233840261972987002208454690542538204970878178295840, 374144419179191051249693744953916154187062957310016] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), B0167, B0184, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq0166 : B0166.tree = HexagonCover.NBand.M6900_7100.SplitData.node0166 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0167
  · exact treeEq0184
  · rfl

theorem accepted0166 : B0166.accepted = true := by decide +kernel
theorem checked0166 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node0166 (maskNeeds ![5192298096474866913910771228344705, 618970019642691236961191426, 77919046967349146032132, 5846006723548183536335309995365386419956235657224, 11498821742992352557354354734334311401619472, 233840261972987002208454690542538204970878178295840, 374144419179191051249693744953916154187062957310016]) := by
  rw [← treeEq0166]
  exact B0166.sound accepted0166
#print axioms checked0166

end HexagonCover.NBand.M6900_7100.SplitTree.Run0000
