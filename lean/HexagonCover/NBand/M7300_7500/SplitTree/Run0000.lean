import HexagonCover.NBand.M7300_7500.SplitData
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7300_7500.SplitTree.Run0000
open OwnerTree HexagonCover.NBand.M7300_7500

abbrev Block := Chunk (n := 172) (Certificate := Fin 1033) (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck

def B0065 : Block := .branch 168 ![288230376151712129, 755578637260242745820674, 4384504911992708754611054500510032300402620241924, 5846006723548183536335309995365386419956235657224, 58642753197902479917441407571167582946850313961488, 93536104789177807534223263433152627379965000024096, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 347).pointIds 347), (.leaf 3 (Common.fact 348).pointIds 348), (.leaf 4 (Common.fact 349).pointIds 349), (.leaf 5 (Common.fact 350).pointIds 350), (.leaf 6 (Common.fact 351).pointIds 351)]
theorem treeEq0065 : B0065.tree = HexagonCover.NBand.M7300_7500.SplitData.node0065 := by
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

def B0066 : Block := .branch 168 ![288230376151712129, 755578637260242745820674, 4384504911992708754611054500510032300402620241924, 5846006723548183536335309995365386419956235657224, 11874700803313586534923492924246526317860472586256, 140304157183766700916741178080073684008954841399328, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 347).pointIds 347), (.leaf 3 (Common.fact 348).pointIds 348), (.leaf 4 (Common.fact 352).pointIds 352), (.leaf 5 (Common.fact 353).pointIds 353), (.leaf 6 (Common.fact 351).pointIds 351)]
theorem treeEq0066 : B0066.tree = HexagonCover.NBand.M7300_7500.SplitData.node0066 := by
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

def B0064 : Block := .branch 165 ![288230376151712129, 755578637260242745820674, 4384504911992708754611054500510032300402620241924, 5846006723548183536335309995365386419956235657224, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), B0065, B0066, (.leaf 0 [] 0)]
theorem treeEq0064 : B0064.tree = HexagonCover.NBand.M7300_7500.SplitData.node0064 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0065
  · exact treeEq0066
  · rfl

def B0067 : Block := .branch 168 ![288230376151712129, 755578637260242745820674, 4384504911992708754611054500510032300402620241924, 174224571863520570664500254341332505485320, 17720707352637197883219678596684931613328182181904, 93536104789177807534223263433152627379965000024096, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 347).pointIds 347), (.leaf 3 (Common.fact 354).pointIds 354), (.leaf 4 (Common.fact 355).pointIds 355), (.leaf 5 (Common.fact 350).pointIds 350), (.leaf 6 (Common.fact 351).pointIds 351)]
theorem treeEq0067 : B0067.tree = HexagonCover.NBand.M7300_7500.SplitData.node0067 := by
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

def B0063 : Block := .branch 162 ![288230376151712129, 755578637260242745820674, 4384504911992708754611054500510032300402620241924, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854522629268926760207461538606232842337255488] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), B0064, B0067, (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 340).pointIds 340)]
theorem treeEq0063 : B0063.tree = HexagonCover.NBand.M7300_7500.SplitData.node0063 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0064
  · exact treeEq0067
  · rfl
  · rfl

def B0068 : Block := .branch 168 ![288230376151712129, 755578637260242745820674, 1461501637330902918203684835077466261090755155972, 2923003448886377699927862958680365044377189376008, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 356).pointIds 356), (.leaf 3 (Common.fact 357).pointIds 357), (.leaf 4 (Common.fact 352).pointIds 352), (.leaf 5 (Common.fact 350).pointIds 350), (.leaf 6 (Common.fact 351).pointIds 351)]
theorem treeEq0068 : B0068.tree = HexagonCover.NBand.M7300_7500.SplitData.node0068 := by
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

def B0062 : Block := .branch 161 ![288230376151712129, 755578637260242745820674, 1461501637330902918203684835077466261090755155972, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854522629268926760207461538606232842337255488] ![(.leaf 0 (Common.fact 331).pointIds 331), (.leaf 1 (Common.fact 332).pointIds 332), B0063, B0068, (.leaf 4 (Common.fact 333).pointIds 333), (.leaf 5 (Common.fact 334).pointIds 334), (.leaf 6 (Common.fact 335).pointIds 335)]
theorem treeEq0062 : B0062.tree = HexagonCover.NBand.M7300_7500.SplitData.node0062 := by
  change Tree.branch (161 : Fin 172) _ = Tree.branch (161 : Fin 172) _
  apply congrArg (Tree.branch (161 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0063
  · exact treeEq0068
  · rfl
  · rfl
  · rfl

def B0069 : Block := .branch 168 ![288230376151712129, 755578637260242745820674, 1461501637330902918203684835077466261090755155972, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517163483407775333885838817569259478581312] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 356).pointIds 356), (.leaf 3 (Common.fact 358).pointIds 358), (.leaf 4 (Common.fact 352).pointIds 352), (.leaf 5 (Common.fact 350).pointIds 350), (.leaf 6 (Common.fact 359).pointIds 359)]
theorem treeEq0069 : B0069.tree = HexagonCover.NBand.M7300_7500.SplitData.node0069 := by
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

def B0061 : Block := .branch 86 ![288230376151712129, 755578637260242745820674, 1461501637330902918203684835095949033961483671556, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854522629268926760207461538606232842337255488] ![(.leaf 0 (Common.fact 326).pointIds 326), (.leaf 1 (Common.fact 327).pointIds 327), (.leaf 2 (Common.fact 328).pointIds 328), B0062, (.leaf 4 (Common.fact 329).pointIds 329), (.leaf 5 (Common.fact 330).pointIds 330), B0069]
theorem treeEq0061 : B0061.tree = HexagonCover.NBand.M7300_7500.SplitData.node0061 := by
  change Tree.branch (86 : Fin 172) _ = Tree.branch (86 : Fin 172) _
  apply congrArg (Tree.branch (86 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0062
  · rfl
  · rfl
  · exact treeEq0069

def B0072 : Block := .branch 168 ![288230376151712129, 755578637260242745820674, 4384504911992708754611054498148849058967797635076, 174224571863678988306263738589820825395208, 17720707352637197883219678596684931613328182181904, 93536104789177807534223263433152627379965000024096, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 362).pointIds 362), (.leaf 3 (Common.fact 363).pointIds 363), (.leaf 4 (Common.fact 355).pointIds 355), (.leaf 5 (Common.fact 350).pointIds 350), (.leaf 6 (Common.fact 351).pointIds 351)]
theorem treeEq0072 : B0072.tree = HexagonCover.NBand.M7300_7500.SplitData.node0072 := by
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

def B0071 : Block := .branch 161 ![288230376151712129, 755578637260242745820674, 1461501637330902918203684832716283019655932549124, 174224571863678988306263738589820825395208, 17720707352637197883219678596684931613328182181904, 93536104789177807534223263433152627379965000024096, 2854522629268926760207461538606232842337255488] ![(.leaf 0 (Common.fact 331).pointIds 331), (.leaf 1 (Common.fact 332).pointIds 332), B0072, (.leaf 3 (Common.fact 361).pointIds 361), (.leaf 4 (Common.fact 333).pointIds 333), (.leaf 5 (Common.fact 334).pointIds 334), (.leaf 6 (Common.fact 335).pointIds 335)]
theorem treeEq0071 : B0071.tree = HexagonCover.NBand.M7300_7500.SplitData.node0071 := by
  change Tree.branch (161 : Fin 172) _ = Tree.branch (161 : Fin 172) _
  apply congrArg (Tree.branch (161 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0072
  · rfl
  · rfl
  · rfl
  · rfl

def B0070 : Block := .branch 162 ![288230376151712129, 755578637260242745820674, 1461501637330902918203684832716283019655932549124, 174224571863678988306263738589820825395208, 11874700803313586210404939265819799534704452010000, 93536104789177807534223263433152627379965000024096, 2854522629268926760207461538606232842337255488] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 360).pointIds 360), B0071, (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 340).pointIds 340)]
theorem treeEq0070 : B0070.tree = HexagonCover.NBand.M7300_7500.SplitData.node0070 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0071
  · rfl
  · rfl

def B0060 : Block := .branch 71 ![288230376151712129, 755578637260242745820674, 1461501637330902918203684832734765792526661064708, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854522629268926760207461538606232842337255488] ![(.leaf 0 (Common.fact 322).pointIds 322), (.leaf 1 (Common.fact 323).pointIds 323), B0061, B0070, (.leaf 4 (Common.fact 324).pointIds 324), (.leaf 5 (Common.fact 325).pointIds 325), (.leaf 0 [] 0)]
theorem treeEq0060 : B0060.tree = HexagonCover.NBand.M7300_7500.SplitData.node0060 := by
  change Tree.branch (71 : Fin 172) _ = Tree.branch (71 : Fin 172) _
  apply congrArg (Tree.branch (71 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0061
  · exact treeEq0070
  · rfl
  · rfl
  · rfl

def B0059 : Block := .branch 91 ![288230376151712129, 755578637260242745820674, 1461501637330902918203684832734765792526661064708, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854522629268926757731581460035472292539007040] ![(.leaf 0 (Common.fact 316).pointIds 316), (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 320).pointIds 320), (.leaf 5 (Common.fact 321).pointIds 321), B0060]
theorem treeEq0059 : B0059.tree = HexagonCover.NBand.M7300_7500.SplitData.node0059 := by
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
  · exact treeEq0060

def B0058 : Block := .branch 102 ![288230376151712129, 755578637260242745820674, 1461501637330902918203684832734765792526661064708, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854522629268921687129180547117866305726185536] ![(.leaf 0 (Common.fact 310).pointIds 310), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), (.leaf 3 (Common.fact 313).pointIds 313), (.leaf 4 (Common.fact 314).pointIds 314), (.leaf 5 (Common.fact 315).pointIds 315), B0059]
theorem treeEq0058 : B0058.tree = HexagonCover.NBand.M7300_7500.SplitData.node0058 := by
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
  · exact treeEq0059

def B0057 : Block := .branch 108 ![288230376151712129, 755578637260242745820674, 1461501637330902918203684832734765792526661064708, 174224571863678988303902555348386002788360, 11874700803313586210404939265819799534704452010000, 93536104789177807534223263433152627379965000024096, 2854522629279306280846250202374927298384625728] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), B0058, (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 309).pointIds 309)]
theorem treeEq0057 : B0057.tree = HexagonCover.NBand.M7300_7500.SplitData.node0057 := by
  change Tree.branch (108 : Fin 172) _ = Tree.branch (108 : Fin 172) _
  apply congrArg (Tree.branch (108 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0058
  · rfl
  · rfl

def B0056 : Block := .branch 119 ![288230376151712129, 755578637260242745820674, 1461501637330902918203684832734765792526661064708, 174224571863678988303902555348386002788360, 11874700803313586210404939265819799534704452010000, 93536104789177807534223263433152627379965000024096, 2854522629279306280846250202374927298384625728] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), B0057, (.leaf 5 (Common.fact 151).pointIds 151), (.leaf 6 (Common.fact 303).pointIds 303)]
theorem treeEq0056 : B0056.tree = HexagonCover.NBand.M7300_7500.SplitData.node0056 := by
  change Tree.branch (119 : Fin 172) _ = Tree.branch (119 : Fin 172) _
  apply congrArg (Tree.branch (119 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0057
  · rfl
  · rfl

def B0055 : Block := .branch 129 ![288230376151712129, 755578637260242745820674, 1461501637330902918203684832734765792526661064708, 174224571863758216466416819685979546738696, 11874700803313586210404939265819799534704452010000, 93536104789177807534223263433152627379965000024096, 2854522629279306280846250202374927298384625728] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 298).pointIds 298), (.leaf 2 (Common.fact 299).pointIds 299), (.leaf 3 (Common.fact 300).pointIds 300), B0056, (.leaf 5 (Common.fact 301).pointIds 301), (.leaf 6 (Common.fact 302).pointIds 302)]
theorem treeEq0055 : B0055.tree = HexagonCover.NBand.M7300_7500.SplitData.node0055 := by
  change Tree.branch (129 : Fin 172) _ = Tree.branch (129 : Fin 172) _
  apply congrArg (Tree.branch (129 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0056
  · rfl
  · rfl

def B0054 : Block := .branch 77 ![288230376151712129, 604462909808414098982402, 1461501637330902918203684832734765792526661064708, 174224571863758216466416819685979546738696, 11874700803313586210404939265819799534704452010000, 93536104789177807534223263433152627379965000024096, 2854522629279306280846250202374927298384625728] ![(.leaf 0 (Common.fact 291).pointIds 291), B0055, (.leaf 2 (Common.fact 292).pointIds 292), (.leaf 3 (Common.fact 293).pointIds 293), (.leaf 4 (Common.fact 294).pointIds 294), (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 6 (Common.fact 296).pointIds 296)]
theorem treeEq0054 : B0054.tree = HexagonCover.NBand.M7300_7500.SplitData.node0054 := by
  change Tree.branch (77 : Fin 172) _ = Tree.branch (77 : Fin 172) _
  apply congrArg (Tree.branch (77 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0055
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0053 : Block := .branch 160 ![288230376151712129, 604462981866008136910338, 18482772870728521732, 174224571863758216466416819685979546738696, 11874700803313586210404939265819799534704452010000, 93536104789177807534223263433152627379965000024096, 2854522629279306280846250202374927298384625728] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), B0054, (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 290).pointIds 290)]
theorem treeEq0053 : B0053.tree = HexagonCover.NBand.M7300_7500.SplitData.node0053 := by
  change Tree.branch (160 : Fin 172) _ = Tree.branch (160 : Fin 172) _
  apply congrArg (Tree.branch (160 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0054
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0053 : B0053.accepted = true := by decide +kernel
theorem checked0053 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node0053 (maskNeeds ![288230376151712129, 604462981866008136910338, 18482772870728521732, 174224571863758216466416819685979546738696, 11874700803313586210404939265819799534704452010000, 93536104789177807534223263433152627379965000024096, 2854522629279306280846250202374927298384625728]) := by
  rw [← treeEq0053]
  exact B0053.sound accepted0053
#print axioms checked0053

def Tip0033_0053 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node0053 ![288230376151712129, 604462981866008136910338, 18482772870728521732, 174224571863758216466416819685979546738696, 11874700803313586210404939265819799534704452010000, 93536104789177807534223263433152627379965000024096, 2854522629279306280846250202374927298384625728] checked0053
def B0052 : Block := .branch 97 ![288230376151712129, 604462981866008136910338, 18482772870728521732, 174224571863599760141388291010792458838024, 11874700803313586210404939265819799534704452010000, 93536104789177807534223263433152627379965000024096, 2854522629279306280846250202374927298384625728] ![(.leaf 0 (Common.fact 279).pointIds 279), (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 281).pointIds 281), Tip0033_0053, (.leaf 4 (Common.fact 282).pointIds 282), (.leaf 5 (Common.fact 283).pointIds 283), (.leaf 6 (Common.fact 284).pointIds 284)]
theorem treeEq0052 : B0052.tree = HexagonCover.NBand.M7300_7500.SplitData.node0052 := by
  change Tree.branch (97 : Fin 172) _ = Tree.branch (97 : Fin 172) _
  apply congrArg (Tree.branch (97 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0051 : Block := .branch 107 ![288230376151712129, 604462981866008136910338, 18482772870728521732, 174224571863599760141388291010792458838024, 11874700803313586210404939265819799534704452010000, 93536104789177807534223263433152627379965000024096, 2854522629279306280846250202374927298384625728] ![(.leaf 0 (Common.fact 273).pointIds 273), (.leaf 1 (Common.fact 274).pointIds 274), (.leaf 2 (Common.fact 275).pointIds 275), B0052, (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 278).pointIds 278)]
theorem treeEq0051 : B0051.tree = HexagonCover.NBand.M7300_7500.SplitData.node0051 := by
  change Tree.branch (107 : Fin 172) _ = Tree.branch (107 : Fin 172) _
  apply congrArg (Tree.branch (107 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0052
  · rfl
  · rfl
  · rfl

def B0050 : Block := .branch 118 ![288230376151712129, 604462981866008136910338, 18482772870728521732, 174224571863599760141388291010792458838024, 11874700803313586210404939265819799534704452010000, 93536104789177807534223263433152627379965000024096, 2854522629279306280846250202374927298384625728] ![(.leaf 0 (Common.fact 267).pointIds 267), (.leaf 1 (Common.fact 268).pointIds 268), (.leaf 2 (Common.fact 269).pointIds 269), B0051, (.leaf 4 (Common.fact 270).pointIds 270), (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 6 (Common.fact 272).pointIds 272)]
theorem treeEq0050 : B0050.tree = HexagonCover.NBand.M7300_7500.SplitData.node0050 := by
  change Tree.branch (118 : Fin 172) _ = Tree.branch (118 : Fin 172) _
  apply congrArg (Tree.branch (118 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0051
  · rfl
  · rfl
  · rfl

def B0049 : Block := .branch 128 ![288230376151712129, 604462981866008136910338, 18482772870728521732, 174224571863599760141388291010792458838024, 11874700803313586210404939265819799534704452010000, 93536104789177807534223263433152627379965000024096, 2854522629279306280846250202374927298384625728] ![(.leaf 0 (Common.fact 261).pointIds 261), (.leaf 1 (Common.fact 262).pointIds 262), (.leaf 2 (Common.fact 263).pointIds 263), B0050, (.leaf 4 (Common.fact 264).pointIds 264), (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 266).pointIds 266)]
theorem treeEq0049 : B0049.tree = HexagonCover.NBand.M7300_7500.SplitData.node0049 := by
  change Tree.branch (128 : Fin 172) _ = Tree.branch (128 : Fin 172) _
  apply congrArg (Tree.branch (128 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0050
  · rfl
  · rfl
  · rfl

def B0048 : Block := .branch 137 ![288230376151712129, 604462981866008136910338, 18482772870728521732, 79266848140492005727134572552, 11874700803313586210404939265819799534704452010000, 93536104789177807534223263433152627379965000024096, 2854522629279306280846250202374927298384625728] ![(.leaf 0 (Common.fact 256).pointIds 256), (.leaf 1 (Common.fact 257).pointIds 257), (.leaf 2 (Common.fact 258).pointIds 258), B0049, (.leaf 4 (Common.fact 259).pointIds 259), (.leaf 5 (Common.fact 260).pointIds 260), (.leaf 0 [] 0)]
theorem treeEq0048 : B0048.tree = HexagonCover.NBand.M7300_7500.SplitData.node0048 := by
  change Tree.branch (137 : Fin 172) _ = Tree.branch (137 : Fin 172) _
  apply congrArg (Tree.branch (137 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0049
  · rfl
  · rfl
  · rfl

def B0047 : Block := .branch 151 ![288230376151712129, 604462981866008136910338, 18482772870728521732, 79266848140492005727134572552, 11874700803313586210404939265819799534704452010000, 93536104789220342830088380741085549205893971050528, 27243867386518729678263475937025619132480] ![(.leaf 0 (Common.fact 250).pointIds 250), (.leaf 1 (Common.fact 251).pointIds 251), (.leaf 2 (Common.fact 252).pointIds 252), (.leaf 3 (Common.fact 253).pointIds 253), (.leaf 4 (Common.fact 254).pointIds 254), (.leaf 5 (Common.fact 255).pointIds 255), B0048]
theorem treeEq0047 : B0047.tree = HexagonCover.NBand.M7300_7500.SplitData.node0047 := by
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
  · exact treeEq0048

def B0046 : Block := .branch 163 ![288230376151712129, 604462981866008136910338, 18482772870728521732, 79266848140492005727134572552, 182687704666362864775460604089535377456991666192, 93536104789220342830088380741085549205893971050528, 27243867386518729678263475937025619132480] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B0047, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 249).pointIds 249)]
theorem treeEq0046 : B0046.tree = HexagonCover.NBand.M7300_7500.SplitData.node0046 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0047
  · rfl
  · rfl

def B0045 : Block := .branch 113 ![288230376151712129, 604462981866008136910338, 18482772870728521732, 79266848140492005727134572552, 182687704666362864775460604089535377456991666192, 93536104789220342830088380741085549205893971050528, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 238).pointIds 238), (.leaf 1 (Common.fact 239).pointIds 239), (.leaf 2 (Common.fact 240).pointIds 240), (.leaf 3 (Common.fact 241).pointIds 241), (.leaf 4 (Common.fact 242).pointIds 242), (.leaf 5 (Common.fact 243).pointIds 243), B0046]
theorem treeEq0045 : B0045.tree = HexagonCover.NBand.M7300_7500.SplitData.node0045 := by
  change Tree.branch (113 : Fin 172) _ = Tree.branch (113 : Fin 172) _
  apply congrArg (Tree.branch (113 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0046

def B0044 : Block := .branch 114 ![288230376151712129, 604462981866008136910338, 18482772870728521732, 79266848140492005727134572552, 182687704666362864775460604089535377456991666192, 93536104789220322060900946601775035083908654170144, 27243857002558837908722333576781312294976] ![(.leaf 0 (Common.fact 232).pointIds 232), (.leaf 1 (Common.fact 233).pointIds 233), (.leaf 2 (Common.fact 234).pointIds 234), (.leaf 3 (Common.fact 235).pointIds 235), (.leaf 4 (Common.fact 236).pointIds 236), B0045, (.leaf 6 (Common.fact 237).pointIds 237)]
theorem treeEq0044 : B0044.tree = HexagonCover.NBand.M7300_7500.SplitData.node0044 := by
  change Tree.branch (114 : Fin 172) _ = Tree.branch (114 : Fin 172) _
  apply congrArg (Tree.branch (114 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0045
  · rfl

def B0043 : Block := .branch 87 ![288230376151712129, 604462981866008136910338, 55376261018147624964, 79266848140492005727134572552, 182687704666362864775460604089535377456991666192, 93536104789220322060900946601775035083908654170144, 27243857002558683166217422904246949904448] ![(.leaf 0 (Common.fact 122).pointIds 122), (.leaf 1 (Common.fact 123).pointIds 123), (.leaf 2 (Common.fact 124).pointIds 124), (.leaf 3 (Common.fact 125).pointIds 125), (.leaf 4 (Common.fact 126).pointIds 126), (.leaf 5 (Common.fact 127).pointIds 127), B0044]
theorem treeEq0043 : B0043.tree = HexagonCover.NBand.M7300_7500.SplitData.node0043 := by
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
  · exact treeEq0044

def B0042 : Block := .branch 65 ![288230376151712129, 604462981866008136910338, 18482772870728521732, 79266848140492005727134572552, 182687704666362864775460604089535377456991666192, 93536104789220322060900946601775035083908654170144, 27243857002558683166217422904246949904448] ![(.leaf 0 (Common.fact 116).pointIds 116), (.leaf 1 (Common.fact 117).pointIds 117), B0043, (.leaf 3 (Common.fact 118).pointIds 118), (.leaf 4 (Common.fact 119).pointIds 119), (.leaf 5 (Common.fact 120).pointIds 120), (.leaf 6 (Common.fact 231).pointIds 231)]
theorem treeEq0042 : B0042.tree = HexagonCover.NBand.M7300_7500.SplitData.node0042 := by
  change Tree.branch (65 : Fin 172) _ = Tree.branch (65 : Fin 172) _
  apply congrArg (Tree.branch (65 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0043
  · rfl
  · rfl
  · rfl
  · rfl

def B0041 : Block := .branch 78 ![288230376151712129, 604462981866008136910338, 18482772870728521732, 79266848140492005727134572552, 182687704666362864775460604089535377456991666192, 93536104789220322060900946601775035083908654170144, 27243857002558683166217422904246949904448] ![(.leaf 0 (Common.fact 134).pointIds 134), B0042, (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), (.leaf 6 (Common.fact 230).pointIds 230)]
theorem treeEq0041 : B0041.tree = HexagonCover.NBand.M7300_7500.SplitData.node0041 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0042
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0040 : Block := .branch 159 ![288230376151712129, 604462981866008136910338, 18482772870728521732, 79266848140492005727134572552, 182687704666362864775460604089535377456991666192, 93536104789220322060900946601775035083908654170144, 27243857002558683166217422904246949904448] ![(.leaf 0 (Common.fact 224).pointIds 224), (.leaf 1 (Common.fact 225).pointIds 225), (.leaf 2 (Common.fact 226).pointIds 226), (.leaf 3 (Common.fact 227).pointIds 227), (.leaf 4 (Common.fact 228).pointIds 228), (.leaf 5 (Common.fact 229).pointIds 229), B0041]
theorem treeEq0040 : B0040.tree = HexagonCover.NBand.M7300_7500.SplitData.node0040 := by
  change Tree.branch (159 : Fin 172) _ = Tree.branch (159 : Fin 172) _
  apply congrArg (Tree.branch (159 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0041

def B0039 : Block := .branch 79 ![288230376151712129, 72058693549557250, 18482772870728521732, 79266848140492005727134572552, 182687704666362864775460604089535377456991666192, 93536104789220322060900946601775035083908654170144, 27243857002558683166217422904246949904448] ![(.leaf 0 (Common.fact 218).pointIds 218), B0040, (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), (.leaf 6 (Common.fact 223).pointIds 223)]
theorem treeEq0039 : B0039.tree = HexagonCover.NBand.M7300_7500.SplitData.node0039 := by
  change Tree.branch (79 : Fin 172) _ = Tree.branch (79 : Fin 172) _
  apply congrArg (Tree.branch (79 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0040
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0038 : Block := .branch 138 ![288230376151712129, 72058693549557250, 18482772870728521732, 79266848140492005727134572552, 182687704666362864775460604089535377456991666192, 93536104789220322060900946601775035083908654170144, 27243857002558683166217422904246949904448] ![(.leaf 0 (Common.fact 110).pointIds 110), (.leaf 1 (Common.fact 111).pointIds 111), (.leaf 2 (Common.fact 112).pointIds 112), (.leaf 3 (Common.fact 113).pointIds 113), B0039, (.leaf 5 (Common.fact 114).pointIds 114), (.leaf 6 (Common.fact 217).pointIds 217)]
theorem treeEq0038 : B0038.tree = HexagonCover.NBand.M7300_7500.SplitData.node0038 := by
  change Tree.branch (138 : Fin 172) _ = Tree.branch (138 : Fin 172) _
  apply congrArg (Tree.branch (138 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0039
  · rfl
  · rfl

def B0037 : Block := .branch 141 ![288230376151712129, 72058693549557250, 18482772870728521732, 79266848140492005727134572552, 182687704666362864775460604089535377456991666192, 93536104789220322060900946601775035083908654170144, 27243857002558683166217422904246949904448] ![(.leaf 0 (Common.fact 92).pointIds 92), (.leaf 1 (Common.fact 93).pointIds 93), (.leaf 2 (Common.fact 94).pointIds 94), (.leaf 3 (Common.fact 95).pointIds 95), B0038, (.leaf 5 (Common.fact 96).pointIds 96), (.leaf 6 (Common.fact 216).pointIds 216)]
theorem treeEq0037 : B0037.tree = HexagonCover.NBand.M7300_7500.SplitData.node0037 := by
  change Tree.branch (141 : Fin 172) _ = Tree.branch (141 : Fin 172) _
  apply congrArg (Tree.branch (141 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0038
  · rfl
  · rfl

def B0036 : Block := .branch 124 ![288230376151712129, 72058693549557250, 18482772870728521732, 79266848140492005727134572552, 182687704666362864775460604089535377456991666192, 93536104789220322060900946601775035083908654170144, 27222589354626124512250961991282464391232] ![(.leaf 0 (Common.fact 210).pointIds 210), (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), (.leaf 4 (Common.fact 214).pointIds 214), (.leaf 5 (Common.fact 215).pointIds 215), B0037]
theorem treeEq0036 : B0036.tree = HexagonCover.NBand.M7300_7500.SplitData.node0036 := by
  change Tree.branch (124 : Fin 172) _ = Tree.branch (124 : Fin 172) _
  apply congrArg (Tree.branch (124 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0037

def B0035 : Block := .branch 150 ![288230376151712129, 72058693549557250, 18482772870728521732, 79266848140492005727134572552, 182687704666362864775460604089535377456991666192, 93536104789220322060900946601775035083908654170144, 27222589354626124512250961991282464391232] ![(.leaf 0 (Common.fact 204).pointIds 204), (.leaf 1 (Common.fact 205).pointIds 205), (.leaf 2 (Common.fact 206).pointIds 206), (.leaf 3 (Common.fact 207).pointIds 207), B0036, (.leaf 5 (Common.fact 208).pointIds 208), (.leaf 6 (Common.fact 209).pointIds 209)]
theorem treeEq0035 : B0035.tree = HexagonCover.NBand.M7300_7500.SplitData.node0035 := by
  change Tree.branch (150 : Fin 172) _ = Tree.branch (150 : Fin 172) _
  apply congrArg (Tree.branch (150 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0036
  · rfl
  · rfl

def B0034 : Block := .branch 67 ![288230376151712129, 72058693549557250, 18482772870728521732, 79266848140492005727134572552, 182687704666362864775460604089535377456991666192, 93536104789220322060900946601775035083908654170144, 27222589354626124512250961991282464391232] ![(.leaf 0 (Common.fact 198).pointIds 198), B0035, (.leaf 2 (Common.fact 199).pointIds 199), (.leaf 3 (Common.fact 200).pointIds 200), (.leaf 4 (Common.fact 201).pointIds 201), (.leaf 5 (Common.fact 202).pointIds 202), (.leaf 6 (Common.fact 203).pointIds 203)]
theorem treeEq0034 : B0034.tree = HexagonCover.NBand.M7300_7500.SplitData.node0034 := by
  change Tree.branch (67 : Fin 172) _ = Tree.branch (67 : Fin 172) _
  apply congrArg (Tree.branch (67 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0035
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0033 : Block := .branch 132 ![288230376151712129, 72058693549557250, 18482772870728521732, 79266848140492005727134572552, 183401328512715844715989747074260125025183039504, 93536104789220322060900946601775035083908654170144, 21778071483891109096836968272374173007936] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 196).pointIds 196), (.leaf 5 (Common.fact 197).pointIds 197), B0034]
theorem treeEq0033 : B0033.tree = HexagonCover.NBand.M7300_7500.SplitData.node0033 := by
  change Tree.branch (132 : Fin 172) _ = Tree.branch (132 : Fin 172) _
  apply congrArg (Tree.branch (132 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0034

theorem accepted0033 : B0033.accepted = true := by decide +kernel
theorem checked0033 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node0033 (maskNeeds ![288230376151712129, 72058693549557250, 18482772870728521732, 79266848140492005727134572552, 183401328512715844715989747074260125025183039504, 93536104789220322060900946601775035083908654170144, 21778071483891109096836968272374173007936]) := by
  rw [← treeEq0033]
  exact B0033.sound accepted0033
#print axioms checked0033

def B0112 : Block := .branch 170 ![94266855607843243416434530245027883298303978242433, 1461501637330902918204303802735925710892893734402, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 58642753197902479917441407571167582946850313961488, 748288838313422294120286634350736906063837462396960, 2854517184751050952113765133124147397434802240] ![(.leaf 0 (Common.fact 446).pointIds 446), (.leaf 1 (Common.fact 447).pointIds 447), (.leaf 2 (Common.fact 448).pointIds 448), (.leaf 3 (Common.fact 449).pointIds 449), (.leaf 4 (Common.fact 450).pointIds 450), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 452).pointIds 452)]
theorem treeEq0112 : B0112.tree = HexagonCover.NBand.M7300_7500.SplitData.node0112 := by
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

def B0111 : Block := .branch 169 ![94266855607843243416434530245027883298303978242433, 1461501637330902918204303802735925710892893734402, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 58642753197902479917441407571167582946850313961488, 393248, 2854517184751050952113765133124147397434802240] ![(.leaf 0 (Common.fact 440).pointIds 440), (.leaf 1 (Common.fact 441).pointIds 441), (.leaf 2 (Common.fact 442).pointIds 442), (.leaf 3 (Common.fact 443).pointIds 443), (.leaf 4 (Common.fact 444).pointIds 444), B0112, (.leaf 6 (Common.fact 445).pointIds 445)]
theorem treeEq0111 : B0111.tree = HexagonCover.NBand.M7300_7500.SplitData.node0111 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0112
  · rfl

def B0113 : Block := .branch 170 ![93536104789177791958600338428897971189972715176321, 2192252455996354377305527249074424530583410443778, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 58642753197902479917441407571167582946850313961488, 42535295865117307932921825928971419680, 2854517184751050952113765133124147397434802240] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 454).pointIds 454), (.leaf 2 (Common.fact 448).pointIds 448), (.leaf 3 (Common.fact 449).pointIds 449), (.leaf 4 (Common.fact 450).pointIds 450), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 452).pointIds 452)]
theorem treeEq0113 : B0113.tree = HexagonCover.NBand.M7300_7500.SplitData.node0113 := by
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

def B0114 : Block := .branch 170 ![93536104789177791958600338428897971189972715176321, 1461501637330902918204303802735925710892893734402, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 58642753197902479917441407571167582946850313961488, 42535295865117307932921825928971419680, 733605335850202510053956181491265657225401073728] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 447).pointIds 447), (.leaf 2 (Common.fact 448).pointIds 448), (.leaf 3 (Common.fact 449).pointIds 449), (.leaf 4 (Common.fact 450).pointIds 450), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 456).pointIds 456)]
theorem treeEq0114 : B0114.tree = HexagonCover.NBand.M7300_7500.SplitData.node0114 := by
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

def B0110 : Block := .branch 159 ![93536104789177791958600338428897971189972715176321, 1461501637330902918204303802735925710892893734402, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 58642753197902479917441407571167582946850313961488, 42535295865117307932921825928971419680, 2854517184751050952113765133124147397434802240] ![B0111, B0113, (.leaf 2 (Common.fact 226).pointIds 226), (.leaf 3 (Common.fact 227).pointIds 227), (.leaf 4 (Common.fact 228).pointIds 228), (.leaf 5 (Common.fact 229).pointIds 229), B0114]
theorem treeEq0110 : B0110.tree = HexagonCover.NBand.M7300_7500.SplitData.node0110 := by
  change Tree.branch (159 : Fin 172) _ = Tree.branch (159 : Fin 172) _
  apply congrArg (Tree.branch (159 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0111
  · exact treeEq0113
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0114

def B0115 : Block := .branch 170 ![5193564509135055857931993032425857, 1461501637330902918204303802735925710892893734402, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 58642753197902479917441407571167582946850313961488, 93536104789177786765035829293842113257979683143712, 2854517184751050952113765133124147397434802240] ![(.leaf 0 (Common.fact 457).pointIds 457), (.leaf 1 (Common.fact 447).pointIds 447), (.leaf 2 (Common.fact 448).pointIds 448), (.leaf 3 (Common.fact 449).pointIds 449), (.leaf 4 (Common.fact 450).pointIds 450), (.leaf 5 (Common.fact 458).pointIds 458), (.leaf 6 (Common.fact 452).pointIds 452)]
theorem treeEq0115 : B0115.tree = HexagonCover.NBand.M7300_7500.SplitData.node0115 := by
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

def B0109 : Block := .branch 166 ![5193564509135055857931993032425857, 1461501637330902918204303802735925710892893734402, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 58642753197902479917441407571167582946850313961488, 42535295865117307932921825928971419680, 2854517184751050952113765133124147397434802240] ![B0110, (.leaf 1 (Common.fact 187).pointIds 187), (.leaf 2 (Common.fact 188).pointIds 188), (.leaf 3 (Common.fact 189).pointIds 189), (.leaf 4 (Common.fact 190).pointIds 190), B0115, (.leaf 6 (Common.fact 439).pointIds 439)]
theorem treeEq0109 : B0109.tree = HexagonCover.NBand.M7300_7500.SplitData.node0109 := by
  change Tree.branch (166 : Fin 172) _ = Tree.branch (166 : Fin 172) _
  apply congrArg (Tree.branch (166 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0110
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0115
  · rfl

def B0116 : Block := .branch 170 ![5193564509135055857931993032425857, 1461501637330902918204303802735925710892893734402, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 11874700803313586534923492924246526317860472586256, 46768052394631428678383031954853978454918812794912, 2854517184751050952113765133124147397434802240] ![(.leaf 0 (Common.fact 457).pointIds 457), (.leaf 1 (Common.fact 447).pointIds 447), (.leaf 2 (Common.fact 448).pointIds 448), (.leaf 3 (Common.fact 449).pointIds 449), (.leaf 4 (Common.fact 459).pointIds 459), (.leaf 5 (Common.fact 460).pointIds 460), (.leaf 6 (Common.fact 452).pointIds 452)]
theorem treeEq0116 : B0116.tree = HexagonCover.NBand.M7300_7500.SplitData.node0116 := by
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

def B0108 : Block := .branch 165 ![5193564509135055857931993032425857, 1461501637330902918204303802735925710892893734402, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 11874700803313586534923492924246526317860472586256, 42535295865117307932921825928971419680, 2854517184751050952113765133124147397434802240] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), B0109, B0116, (.leaf 0 [] 0)]
theorem treeEq0108 : B0108.tree = HexagonCover.NBand.M7300_7500.SplitData.node0108 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0109
  · exact treeEq0116
  · rfl

def B0117 : Block := .branch 170 ![5193564509135055857931993032425857, 1461501637330902918204303802735925710892893734402, 2923003274661805836407369743351613006661011118084, 174224571863520570664500254341332505485320, 17720707352637197883219678596684931613328182181904, 42535295865117307932921825928971419680, 2854517184751050952113765133124147397434802240] ![(.leaf 0 (Common.fact 457).pointIds 457), (.leaf 1 (Common.fact 447).pointIds 447), (.leaf 2 (Common.fact 448).pointIds 448), (.leaf 3 (Common.fact 461).pointIds 461), (.leaf 4 (Common.fact 462).pointIds 462), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 452).pointIds 452)]
theorem treeEq0117 : B0117.tree = HexagonCover.NBand.M7300_7500.SplitData.node0117 := by
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

def B0107 : Block := .branch 162 ![5193564509135055857931993032425857, 1461501637330902918204303802735925710892893734402, 2923003274661805836407369743351613006661011118084, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 42535295865117307932921825928971419680, 2860092371050683607899149062692309487811297344] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), B0108, B0117, (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 438).pointIds 438)]
theorem treeEq0107 : B0107.tree = HexagonCover.NBand.M7300_7500.SplitData.node0107 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0108
  · exact treeEq0117
  · rfl
  · rfl

def B0118 : Block := .branch 170 ![5193564509135055857931993032425857, 1461501637330902918204303802735925710892893734402, 77919046967349146032132, 2923003448886377699927862958680365044377189376008, 11874700803313586534923492924246526317860472586256, 42535295865117307932921825928971419680, 2854517184751050952113765133124147397434802240] ![(.leaf 0 (Common.fact 457).pointIds 457), (.leaf 1 (Common.fact 447).pointIds 447), (.leaf 2 (Common.fact 463).pointIds 463), (.leaf 3 (Common.fact 464).pointIds 464), (.leaf 4 (Common.fact 459).pointIds 459), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 452).pointIds 452)]
theorem treeEq0118 : B0118.tree = HexagonCover.NBand.M7300_7500.SplitData.node0118 := by
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

def B0106 : Block := .branch 161 ![5193564509135055857931993032425857, 1461501637330902918204303802735925710892893734402, 77919046967349146032132, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 42535295865117307932921825928971419680, 2860092371050683607899149062692309487811297344] ![(.leaf 0 (Common.fact 331).pointIds 331), (.leaf 1 (Common.fact 332).pointIds 332), B0107, B0118, (.leaf 4 (Common.fact 333).pointIds 333), (.leaf 5 (Common.fact 334).pointIds 334), (.leaf 6 (Common.fact 437).pointIds 437)]
theorem treeEq0106 : B0106.tree = HexagonCover.NBand.M7300_7500.SplitData.node0106 := by
  change Tree.branch (161 : Fin 172) _ = Tree.branch (161 : Fin 172) _
  apply congrArg (Tree.branch (161 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0107
  · exact treeEq0118
  · rfl
  · rfl
  · rfl

def B0119 : Block := .branch 170 ![5192298096474866913910771228344705, 1461501637330902918204303802735925710892893734402, 77919046967349146032132, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 42535295865117307932921825928971419680, 2854517184751052219764365361353548894138007616] ![(.leaf 0 (Common.fact 465).pointIds 465), (.leaf 1 (Common.fact 447).pointIds 447), (.leaf 2 (Common.fact 463).pointIds 463), (.leaf 3 (Common.fact 461).pointIds 461), (.leaf 4 (Common.fact 459).pointIds 459), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq0119 : B0119.tree = HexagonCover.NBand.M7300_7500.SplitData.node0119 := by
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

def B0105 : Block := .branch 100 ![5192298096474866913910771228344705, 1461501637330902918204303802735925710892893734402, 77919046967349146032132, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 42535295865117307932921825928971419680, 2860092371050683607899149062692309487811297344] ![B0106, (.leaf 1 (Common.fact 432).pointIds 432), (.leaf 2 (Common.fact 433).pointIds 433), (.leaf 3 (Common.fact 434).pointIds 434), (.leaf 4 (Common.fact 435).pointIds 435), (.leaf 5 (Common.fact 436).pointIds 436), B0119]
theorem treeEq0105 : B0105.tree = HexagonCover.NBand.M7300_7500.SplitData.node0105 := by
  change Tree.branch (100 : Fin 172) _ = Tree.branch (100 : Fin 172) _
  apply congrArg (Tree.branch (100 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0106
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0119

def B0120 : Block := .branch 170 ![5192296859139290538337810916573569, 1461501637330902918204303802735925710892893734402, 77919046967349146032132, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 42535295865117307932921825928971419680, 2854517184751050953042220162588182603609145408] ![(.leaf 0 (Common.fact 467).pointIds 467), (.leaf 1 (Common.fact 447).pointIds 447), (.leaf 2 (Common.fact 463).pointIds 463), (.leaf 3 (Common.fact 461).pointIds 461), (.leaf 4 (Common.fact 459).pointIds 459), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 468).pointIds 468)]
theorem treeEq0120 : B0120.tree = HexagonCover.NBand.M7300_7500.SplitData.node0120 := by
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

def B0104 : Block := .branch 90 ![5192296859139290538337810916573569, 1461501637330902918204303802735925710892893734402, 77919046967349146032132, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 42535295865117307932921825928971419680, 2860092371050683607899149062692309487811297344] ![B0105, (.leaf 1 (Common.fact 427).pointIds 427), (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), (.leaf 4 (Common.fact 430).pointIds 430), (.leaf 5 (Common.fact 431).pointIds 431), B0120]
theorem treeEq0104 : B0104.tree = HexagonCover.NBand.M7300_7500.SplitData.node0104 := by
  change Tree.branch (90 : Fin 172) _ = Tree.branch (90 : Fin 172) _
  apply congrArg (Tree.branch (90 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0105
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0120

def B0121 : Block := .branch 170 ![5192296859139290538337810916573569, 618970019642691236961191426, 1461501637330902918203684835077466261090755155972, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 42535295865117307932921825928971419680, 2854517184751050952113765133124147397434802240] ![(.leaf 0 (Common.fact 467).pointIds 467), (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 461).pointIds 461), (.leaf 4 (Common.fact 459).pointIds 459), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 452).pointIds 452)]
theorem treeEq0121 : B0121.tree = HexagonCover.NBand.M7300_7500.SplitData.node0121 := by
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

def B0103 : Block := .branch 160 ![5192296859139290538337810916573569, 618970019642691236961191426, 77919046967349146032132, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 42535295865117307932921825928971419680, 2860092371050683607899149062692309487811297344] ![(.leaf 0 (Common.fact 285).pointIds 285), B0104, B0121, (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 426).pointIds 426)]
theorem treeEq0103 : B0103.tree = HexagonCover.NBand.M7300_7500.SplitData.node0103 := by
  change Tree.branch (160 : Fin 172) _ = Tree.branch (160 : Fin 172) _
  apply congrArg (Tree.branch (160 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0104
  · exact treeEq0121
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0103 : B0103.accepted = true := by decide +kernel
theorem checked0103 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node0103 (maskNeeds ![5192296859139290538337810916573569, 618970019642691236961191426, 77919046967349146032132, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 42535295865117307932921825928971419680, 2860092371050683607899149062692309487811297344]) := by
  rw [← treeEq0103]
  exact B0103.sound accepted0103
#print axioms checked0103

def B0159 : Block := .branch 171 ![94266855607843243416434530245027883298303978242433, 1461501637330902918204303802735925710892893734402, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 182699203488105857128017958444269711768393187344, 982129100286366761032876207585342189208786669273120, 22479903864714961470063917021614029930560] ![(.leaf 0 (Common.fact 529).pointIds 529), (.leaf 1 (Common.fact 530).pointIds 530), (.leaf 2 (Common.fact 531).pointIds 531), (.leaf 3 (Common.fact 532).pointIds 532), (.leaf 4 (Common.fact 533).pointIds 533), (.leaf 5 (Common.fact 534).pointIds 534), (.leaf 6 (Common.fact 535).pointIds 535)]
theorem treeEq0159 : B0159.tree = HexagonCover.NBand.M7300_7500.SplitData.node0159 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0160 : Block := .branch 171 ![94266855607843243416434530245027883298303978242433, 618970019642691236961191426, 4384504911992708754611054500510032300402620241924, 5846006723548183536335309995365386419956235657224, 182699203488105857128017958444269711768393187344, 982129100286366761032876207585342189208786669273120, 22479903864714961470063917021614029930560] ![(.leaf 0 (Common.fact 529).pointIds 529), (.leaf 1 (Common.fact 536).pointIds 536), (.leaf 2 (Common.fact 537).pointIds 537), (.leaf 3 (Common.fact 532).pointIds 532), (.leaf 4 (Common.fact 533).pointIds 533), (.leaf 5 (Common.fact 534).pointIds 534), (.leaf 6 (Common.fact 535).pointIds 535)]
theorem treeEq0160 : B0160.tree = HexagonCover.NBand.M7300_7500.SplitData.node0160 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0161 : Block := .branch 171 ![94266855607843243416434530245027883298303978242433, 618970019642691236961191426, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 182699203488105857128017958444269711768393187344, 982129100286366761032876207585342189208786669273120, 1461501659810806782918336817770378696201237692480] ![(.leaf 0 (Common.fact 529).pointIds 529), (.leaf 1 (Common.fact 536).pointIds 536), (.leaf 2 (Common.fact 531).pointIds 531), (.leaf 3 (Common.fact 532).pointIds 532), (.leaf 4 (Common.fact 533).pointIds 533), (.leaf 5 (Common.fact 534).pointIds 534), (.leaf 6 (Common.fact 538).pointIds 538)]
theorem treeEq0161 : B0161.tree = HexagonCover.NBand.M7300_7500.SplitData.node0161 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0158 : Block := .branch 160 ![94266855607843243416434530245027883298303978242433, 618970019642691236961191426, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 182699203488105857128017958444269711768393187344, 982129100286366761032876207585342189208786669273120, 22479903864714961470063917021614029930560] ![(.leaf 0 (Common.fact 285).pointIds 285), B0159, B0160, (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), B0161]
theorem treeEq0158 : B0158.tree = HexagonCover.NBand.M7300_7500.SplitData.node0158 := by
  change Tree.branch (160 : Fin 172) _ = Tree.branch (160 : Fin 172) _
  apply congrArg (Tree.branch (160 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0159
  · exact treeEq0160
  · rfl
  · rfl
  · rfl
  · exact treeEq0161

def B0162 : Block := .branch 171 ![93536104789177791958600338428897971189972715176321, 730750818665451459101842416358141510927477900802, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 182699203488105857128017958444269711768393187344, 982129100286366761032876207585342189208786669273120, 22479903864714961470063917021614029930560] ![(.leaf 0 (Common.fact 539).pointIds 539), (.leaf 1 (Common.fact 540).pointIds 540), (.leaf 2 (Common.fact 531).pointIds 531), (.leaf 3 (Common.fact 532).pointIds 532), (.leaf 4 (Common.fact 533).pointIds 533), (.leaf 5 (Common.fact 534).pointIds 534), (.leaf 6 (Common.fact 535).pointIds 535)]
theorem treeEq0162 : B0162.tree = HexagonCover.NBand.M7300_7500.SplitData.node0162 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0163 : Block := .branch 171 ![93536104789177791958600338428897971189972715176321, 618970019642691236961191426, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 182699203488105857128017958444269711768393187344, 982129100286366761032876207585342189208786669273120, 730750841145355323816803886422058531441996202048] ![(.leaf 0 (Common.fact 539).pointIds 539), (.leaf 1 (Common.fact 536).pointIds 536), (.leaf 2 (Common.fact 531).pointIds 531), (.leaf 3 (Common.fact 532).pointIds 532), (.leaf 4 (Common.fact 533).pointIds 533), (.leaf 5 (Common.fact 534).pointIds 534), (.leaf 6 (Common.fact 541).pointIds 541)]
theorem treeEq0163 : B0163.tree = HexagonCover.NBand.M7300_7500.SplitData.node0163 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0157 : Block := .branch 159 ![93536104789177791958600338428897971189972715176321, 618970019642691236961191426, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 182699203488105857128017958444269711768393187344, 982129100286366761032876207585342189208786669273120, 22479903864714961470063917021614029930560] ![B0158, B0162, (.leaf 2 (Common.fact 226).pointIds 226), (.leaf 3 (Common.fact 227).pointIds 227), (.leaf 4 (Common.fact 228).pointIds 228), (.leaf 5 (Common.fact 229).pointIds 229), B0163]
theorem treeEq0157 : B0157.tree = HexagonCover.NBand.M7300_7500.SplitData.node0157 := by
  change Tree.branch (159 : Fin 172) _ = Tree.branch (159 : Fin 172) _
  apply congrArg (Tree.branch (159 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0158
  · exact treeEq0162
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0163

def B0164 : Block := .branch 171 ![93536104789177791957333925768709027168750911095169, 1267650600228229402596214834690, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 182699203488105857128017958444269711768393187344, 982129100286366761032876207585342189208786669273120, 22479903864714961470063917021614029930560] ![(.leaf 0 (Common.fact 542).pointIds 542), (.leaf 1 (Common.fact 543).pointIds 543), (.leaf 2 (Common.fact 531).pointIds 531), (.leaf 3 (Common.fact 532).pointIds 532), (.leaf 4 (Common.fact 533).pointIds 533), (.leaf 5 (Common.fact 534).pointIds 534), (.leaf 6 (Common.fact 535).pointIds 535)]
theorem treeEq0164 : B0164.tree = HexagonCover.NBand.M7300_7500.SplitData.node0164 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0165 : Block := .branch 171 ![93536104789177791957333925768709027168750911095169, 618970019642691236961191426, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 182699203488105857128017958444269711768393187344, 982129100286366761032876207585342189208786669273120, 22479903865982612070292146423110733135936] ![(.leaf 0 (Common.fact 542).pointIds 542), (.leaf 1 (Common.fact 536).pointIds 536), (.leaf 2 (Common.fact 531).pointIds 531), (.leaf 3 (Common.fact 532).pointIds 532), (.leaf 4 (Common.fact 533).pointIds 533), (.leaf 5 (Common.fact 534).pointIds 534), (.leaf 6 (Common.fact 544).pointIds 544)]
theorem treeEq0165 : B0165.tree = HexagonCover.NBand.M7300_7500.SplitData.node0165 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0156 : Block := .branch 100 ![93536104789177791957333925768709027168750911095169, 618970019642691236961191426, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 182699203488105857128017958444269711768393187344, 982129100286366761032876207585342189208786669273120, 22479903864714961470063917021614029930560] ![B0157, B0164, (.leaf 2 (Common.fact 433).pointIds 433), (.leaf 3 (Common.fact 434).pointIds 434), (.leaf 4 (Common.fact 435).pointIds 435), (.leaf 5 (Common.fact 436).pointIds 436), B0165]
theorem treeEq0156 : B0156.tree = HexagonCover.NBand.M7300_7500.SplitData.node0156 := by
  change Tree.branch (100 : Fin 172) _ = Tree.branch (100 : Fin 172) _
  apply congrArg (Tree.branch (100 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0157
  · exact treeEq0164
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0165

def B0166 : Block := .branch 171 ![5192298096474866913910771228344705, 618970019642691236961191426, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 182699203488105857128017958444269711768393187344, 327376366762122253677625402528447396402928890019872, 22479903864714961470063917021614029930560] ![(.leaf 0 (Common.fact 545).pointIds 545), (.leaf 1 (Common.fact 536).pointIds 536), (.leaf 2 (Common.fact 531).pointIds 531), (.leaf 3 (Common.fact 532).pointIds 532), (.leaf 4 (Common.fact 533).pointIds 533), (.leaf 5 (Common.fact 546).pointIds 546), (.leaf 6 (Common.fact 535).pointIds 535)]
theorem treeEq0166 : B0166.tree = HexagonCover.NBand.M7300_7500.SplitData.node0166 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0155 : Block := .branch 166 ![5192298096474866913910771228344705, 618970019642691236961191426, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 182699203488105857128017958444269711768393187344, 982129100286366761032876207585342189208786669273120, 22479903865031874120120974371988205731904] ![B0156, (.leaf 1 (Common.fact 187).pointIds 187), (.leaf 2 (Common.fact 188).pointIds 188), (.leaf 3 (Common.fact 189).pointIds 189), (.leaf 4 (Common.fact 190).pointIds 190), B0166, (.leaf 6 (Common.fact 439).pointIds 439)]
theorem treeEq0155 : B0155.tree = HexagonCover.NBand.M7300_7500.SplitData.node0155 := by
  change Tree.branch (166 : Fin 172) _ = Tree.branch (166 : Fin 172) _
  apply congrArg (Tree.branch (166 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0156
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0166
  · rfl

def B0167 : Block := .branch 171 ![5192298096474866913910771228344705, 618970019642691236961191426, 77919046967349146032132, 8769009998209989372742602289545497123000919547912, 182699203488105857128017958444269711768393187344, 982129100286366761032876207585342189208786669273120, 22479903864714961470063917021614029930560] ![(.leaf 0 (Common.fact 545).pointIds 545), (.leaf 1 (Common.fact 536).pointIds 536), (.leaf 2 (Common.fact 547).pointIds 547), (.leaf 3 (Common.fact 548).pointIds 548), (.leaf 4 (Common.fact 533).pointIds 533), (.leaf 5 (Common.fact 534).pointIds 534), (.leaf 6 (Common.fact 535).pointIds 535)]
theorem treeEq0167 : B0167.tree = HexagonCover.NBand.M7300_7500.SplitData.node0167 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0154 : Block := .branch 161 ![5192298096474866913910771228344705, 618970019642691236961191426, 77919046967349146032132, 5846006723548183536335309995365386419956235657224, 182699203488105857128017958444269711768393187344, 982129100286366761032876207585342189208786669273120, 22479903865031874120120974371988205731904] ![(.leaf 0 (Common.fact 331).pointIds 331), (.leaf 1 (Common.fact 332).pointIds 332), B0155, B0167, (.leaf 4 (Common.fact 333).pointIds 333), (.leaf 5 (Common.fact 334).pointIds 334), (.leaf 6 (Common.fact 528).pointIds 528)]
theorem treeEq0154 : B0154.tree = HexagonCover.NBand.M7300_7500.SplitData.node0154 := by
  change Tree.branch (161 : Fin 172) _ = Tree.branch (161 : Fin 172) _
  apply congrArg (Tree.branch (161 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0155
  · exact treeEq0167
  · rfl
  · rfl
  · rfl

def B0168 : Block := .branch 171 ![5192298096474866913910771228344705, 618970019642691236961191426, 77919046967349146032132, 5846006549663894039735755165580962022322679603208, 182699029263533993607524665196470706703068921872, 982129100286366761032876207585342189208786669273120, 22479903864714961470063917021614029930560] ![(.leaf 0 (Common.fact 545).pointIds 545), (.leaf 1 (Common.fact 536).pointIds 536), (.leaf 2 (Common.fact 547).pointIds 547), (.leaf 3 (Common.fact 549).pointIds 549), (.leaf 4 (Common.fact 550).pointIds 550), (.leaf 5 (Common.fact 534).pointIds 534), (.leaf 6 (Common.fact 535).pointIds 535)]
theorem treeEq0168 : B0168.tree = HexagonCover.NBand.M7300_7500.SplitData.node0168 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0153 : Block := .branch 137 ![5192298096474866913910771228344705, 618970019642691236961191426, 77919046967349146032132, 5846006549663894039735755165580962022322679603208, 182699203488105857128017958444269711768393187344, 982129100286366761032876207585342189208786669273120, 22479903865031874120120974371988205731904] ![(.leaf 0 (Common.fact 256).pointIds 256), (.leaf 1 (Common.fact 257).pointIds 257), (.leaf 2 (Common.fact 258).pointIds 258), B0154, B0168, (.leaf 5 (Common.fact 260).pointIds 260), (.leaf 0 [] 0)]
theorem treeEq0153 : B0153.tree = HexagonCover.NBand.M7300_7500.SplitData.node0153 := by
  change Tree.branch (137 : Fin 172) _ = Tree.branch (137 : Fin 172) _
  apply congrArg (Tree.branch (137 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0154
  · exact treeEq0168
  · rfl
  · rfl

def B0169 : Block := .branch 171 ![10384594955009694542441267557564801, 618970019642691236961191426, 77919046967349146032132, 5846006549663894039735755165580962022322679603208, 182699203488105857128017958444269711768393187344, 982129100286366761032876207585342189208786669273120, 22479909057011820004891545552110359150656] ![(.leaf 0 (Common.fact 551).pointIds 551), (.leaf 1 (Common.fact 536).pointIds 536), (.leaf 2 (Common.fact 547).pointIds 547), (.leaf 3 (Common.fact 549).pointIds 549), (.leaf 4 (Common.fact 533).pointIds 533), (.leaf 5 (Common.fact 534).pointIds 534), (.leaf 6 (Common.fact 552).pointIds 552)]
theorem treeEq0169 : B0169.tree = HexagonCover.NBand.M7300_7500.SplitData.node0169 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0152 : Block := .branch 112 ![10384594955009694542441267557564801, 618970019642691236961191426, 77919046967349146032132, 5846006549663894039735755165580962022322679603208, 182699203488105857128017958444269711768393187344, 982129100286366761032876207585342189208786669273120, 22479903865031874120120974371988205731904] ![B0153, (.leaf 1 (Common.fact 421).pointIds 421), (.leaf 2 (Common.fact 422).pointIds 422), (.leaf 3 (Common.fact 423).pointIds 423), (.leaf 4 (Common.fact 424).pointIds 424), (.leaf 5 (Common.fact 425).pointIds 425), B0169]
theorem treeEq0152 : B0152.tree = HexagonCover.NBand.M7300_7500.SplitData.node0152 := by
  change Tree.branch (112 : Fin 172) _ = Tree.branch (112 : Fin 172) _
  apply congrArg (Tree.branch (112 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0153
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0169

def B0170 : Block := .branch 171 ![10387129018874574625671300652204417, 1856910058928071511860315650, 77919046967349146032132, 5846006549663894039735755165580962022322679603208, 182699203488105857128017958444269711768393187344, 982129100286366761032876207585342189208786669273120, 22479903864714961470063917021614029930560] ![(.leaf 0 (Common.fact 553).pointIds 553), (.leaf 1 (Common.fact 554).pointIds 554), (.leaf 2 (Common.fact 547).pointIds 547), (.leaf 3 (Common.fact 549).pointIds 549), (.leaf 4 (Common.fact 533).pointIds 533), (.leaf 5 (Common.fact 534).pointIds 534), (.leaf 6 (Common.fact 535).pointIds 535)]
theorem treeEq0170 : B0170.tree = HexagonCover.NBand.M7300_7500.SplitData.node0170 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0151 : Block := .branch 90 ![10387129018874574625671300652204417, 618970019642691236961191426, 77919046967349146032132, 5846006549663894039735755165580962022322679603208, 182699203488105857128017958444269711768393187344, 982129100286366761032876207585342189208786669273120, 27924422060285443193961694874052517691456] ![B0152, B0170, (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), (.leaf 4 (Common.fact 430).pointIds 430), (.leaf 5 (Common.fact 431).pointIds 431), (.leaf 6 (Common.fact 527).pointIds 527)]
theorem treeEq0151 : B0151.tree = HexagonCover.NBand.M7300_7500.SplitData.node0151 := by
  change Tree.branch (90 : Fin 172) _ = Tree.branch (90 : Fin 172) _
  apply congrArg (Tree.branch (90 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0152
  · exact treeEq0170
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0151 : B0151.accepted = true := by decide +kernel
theorem checked0151 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node0151 (maskNeeds ![10387129018874574625671300652204417, 618970019642691236961191426, 77919046967349146032132, 5846006549663894039735755165580962022322679603208, 182699203488105857128017958444269711768393187344, 982129100286366761032876207585342189208786669273120, 27924422060285443193961694874052517691456]) := by
  rw [← treeEq0151]
  exact B0151.sound accepted0151
#print axioms checked0151

end HexagonCover.NBand.M7300_7500.SplitTree.Run0000
