import HexagonCover.NBand.M7100_7300.SplitData
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7100_7300.SplitTree.Run0000
open OwnerTree HexagonCover.NBand.M7100_7300

abbrev Block := Chunk (n := 173) (Certificate := Fin 933) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def B0065 : Block := .branch 168 ![288230376151712129, 755578637260242745820674, 4384504911992708754611054500510032300402620241924, 5846006723548183536335309995365386419956235657224, 58460065493236117052665946967078047569393322393616, 93536104789177807534223263433152627379965000024096, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 347).pointIds 347), (.leaf 3 (Common.fact 348).pointIds 348), (.leaf 4 (Common.fact 349).pointIds 349), (.leaf 5 (Common.fact 350).pointIds 350), (.leaf 6 (Common.fact 351).pointIds 351)]
theorem treeEq0065 : B0065.tree = HexagonCover.NBand.M7100_7300.SplitData.node0065 := by
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

def B0066 : Block := .branch 168 ![288230376151712129, 755578637260242745820674, 4384504911992708754611054500510032300402620241924, 5846006723548183536335309995365386419956235657224, 11874700803313586534923492924246526317860472586256, 140304157183766700916741178080073684008954841399328, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 347).pointIds 347), (.leaf 3 (Common.fact 348).pointIds 348), (.leaf 4 (Common.fact 352).pointIds 352), (.leaf 5 (Common.fact 353).pointIds 353), (.leaf 6 (Common.fact 351).pointIds 351)]
theorem treeEq0066 : B0066.tree = HexagonCover.NBand.M7100_7300.SplitData.node0066 := by
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

def B0064 : Block := .branch 165 ![288230376151712129, 755578637260242745820674, 4384504911992708754611054500510032300402620241924, 5846006723548183536335309995365386419956235657224, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), B0065, B0066, (.leaf 0 [] 0)]
theorem treeEq0064 : B0064.tree = HexagonCover.NBand.M7100_7300.SplitData.node0064 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
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
theorem treeEq0067 : B0067.tree = HexagonCover.NBand.M7100_7300.SplitData.node0067 := by
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

def B0063 : Block := .branch 162 ![288230376151712129, 755578637260242745820674, 4384504911992708754611054500510032300402620241924, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854528073786797495222876952599951750628638784] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), B0064, B0067, (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 340).pointIds 340)]
theorem treeEq0063 : B0063.tree = HexagonCover.NBand.M7100_7300.SplitData.node0063 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
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
theorem treeEq0068 : B0068.tree = HexagonCover.NBand.M7100_7300.SplitData.node0068 := by
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

def B0062 : Block := .branch 161 ![288230376151712129, 755578637260242745820674, 1461501637330902918203684835077466261090755155972, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 23386880725368233488754180200413128266245549326400] ![(.leaf 0 (Common.fact 331).pointIds 331), (.leaf 1 (Common.fact 332).pointIds 332), B0063, B0068, (.leaf 4 (Common.fact 333).pointIds 333), (.leaf 5 (Common.fact 334).pointIds 334), (.leaf 6 (Common.fact 335).pointIds 335)]
theorem treeEq0062 : B0062.tree = HexagonCover.NBand.M7100_7300.SplitData.node0062 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
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
theorem treeEq0069 : B0069.tree = HexagonCover.NBand.M7100_7300.SplitData.node0069 := by
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

def B0061 : Block := .branch 86 ![288230376151712129, 755578637260242745820674, 1461501637330902918203684835077466261090755155972, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 23386880725368233488754180200413128266245549326400] ![(.leaf 0 (Common.fact 326).pointIds 326), (.leaf 1 (Common.fact 327).pointIds 327), (.leaf 2 (Common.fact 328).pointIds 328), B0062, (.leaf 4 (Common.fact 329).pointIds 329), (.leaf 5 (Common.fact 330).pointIds 330), B0069]
theorem treeEq0061 : B0061.tree = HexagonCover.NBand.M7100_7300.SplitData.node0061 := by
  change Tree.branch (86 : Fin 173) _ = Tree.branch (86 : Fin 173) _
  apply congrArg (Tree.branch (86 : Fin 173))
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
theorem treeEq0072 : B0072.tree = HexagonCover.NBand.M7100_7300.SplitData.node0072 := by
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

def B0071 : Block := .branch 161 ![288230376151712129, 755578637260242745820674, 1461501637330902918203684832716283019655932549124, 174224571863678988306263738589820825395208, 17720707352637197883219678596684931613328182181904, 93536104789177807534223263433152627379965000024096, 23386880714479197747284149369585140828428966559808] ![(.leaf 0 (Common.fact 331).pointIds 331), (.leaf 1 (Common.fact 332).pointIds 332), B0072, (.leaf 3 (Common.fact 361).pointIds 361), (.leaf 4 (Common.fact 333).pointIds 333), (.leaf 5 (Common.fact 334).pointIds 334), (.leaf 6 (Common.fact 335).pointIds 335)]
theorem treeEq0071 : B0071.tree = HexagonCover.NBand.M7100_7300.SplitData.node0071 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0072
  · rfl
  · rfl
  · rfl
  · rfl

def B0070 : Block := .branch 162 ![288230376151712129, 755578637260242745820674, 1461501637330902918203684832716283019655932549124, 174224571863678988306263738589820825395208, 11874700803313586210404939265819799534704452010000, 93536104789177807534223263433152627379965000024096, 23386880725368233488754180200413128266245549326400] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 360).pointIds 360), B0071, (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 340).pointIds 340)]
theorem treeEq0070 : B0070.tree = HexagonCover.NBand.M7100_7300.SplitData.node0070 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0071
  · rfl
  · rfl

def B0060 : Block := .branch 71 ![288230376151712129, 755578637260242745820674, 1461501637330902918203684832716283019655932549124, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 23386880725368233488754180200413128266245549326400] ![(.leaf 0 (Common.fact 322).pointIds 322), (.leaf 1 (Common.fact 323).pointIds 323), B0061, B0070, (.leaf 4 (Common.fact 324).pointIds 324), (.leaf 5 (Common.fact 325).pointIds 325), (.leaf 0 [] 0)]
theorem treeEq0060 : B0060.tree = HexagonCover.NBand.M7100_7300.SplitData.node0060 := by
  change Tree.branch (71 : Fin 173) _ = Tree.branch (71 : Fin 173) _
  apply congrArg (Tree.branch (71 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0061
  · exact treeEq0070
  · rfl
  · rfl
  · rfl

def B0059 : Block := .branch 91 ![288230376151712129, 755578637260242745820674, 1461501637330902918203684832716283019655932549124, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 23386880725368233488751704320334557505695751077952] ![(.leaf 0 (Common.fact 316).pointIds 316), (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 320).pointIds 320), (.leaf 5 (Common.fact 321).pointIds 321), B0060]
theorem treeEq0059 : B0059.tree = HexagonCover.NBand.M7100_7300.SplitData.node0059 := by
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
  · exact treeEq0060

def B0058 : Block := .branch 102 ![288230376151712129, 755578637260242745820674, 1461501637330902918203684832716283019655932549124, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 23386880725368233483681101919421639899708938256448] ![(.leaf 0 (Common.fact 310).pointIds 310), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), (.leaf 3 (Common.fact 313).pointIds 313), (.leaf 4 (Common.fact 314).pointIds 314), (.leaf 5 (Common.fact 315).pointIds 315), B0059]
theorem treeEq0058 : B0058.tree = HexagonCover.NBand.M7100_7300.SplitData.node0058 := by
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
  · exact treeEq0059

def B0057 : Block := .branch 108 ![288230376151712129, 755578637260242745820674, 1461501637330902918203684832716283019655932549124, 174224571863678988303902555348386002788360, 11874700803313586210404939265819799534704452010000, 93536104789177807534223263433152627379965000024096, 23386880730812761739009834404490890679609888079936] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), B0058, (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 309).pointIds 309)]
theorem treeEq0057 : B0057.tree = HexagonCover.NBand.M7100_7300.SplitData.node0057 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0058
  · rfl
  · rfl

def B0056 : Block := .branch 119 ![288230376151712129, 755578637260242745820674, 1461501637330902918203684832716283019655932549124, 174224571863678988303902555348386002788360, 11874700803313586210404939265819799534704452010000, 93536104789177807534223263433152627379965000024096, 23386880730812761739009834404490890679609888079936] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), B0057, (.leaf 5 (Common.fact 157).pointIds 157), (.leaf 6 (Common.fact 303).pointIds 303)]
theorem treeEq0056 : B0056.tree = HexagonCover.NBand.M7100_7300.SplitData.node0056 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0057
  · rfl
  · rfl

def B0055 : Block := .branch 129 ![288230376151712129, 755578637260242745820674, 1461501637330902918203684832716283019655932549124, 174224571863678988303902555348386002788360, 11874700803313586210404939265819799534704452010000, 93536104789177807534223263433152627379965000024096, 23386880730812761739009834404490890679609888079936] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 298).pointIds 298), (.leaf 2 (Common.fact 299).pointIds 299), (.leaf 3 (Common.fact 300).pointIds 300), B0056, (.leaf 5 (Common.fact 301).pointIds 301), (.leaf 6 (Common.fact 302).pointIds 302)]
theorem treeEq0055 : B0055.tree = HexagonCover.NBand.M7100_7300.SplitData.node0055 := by
  change Tree.branch (129 : Fin 173) _ = Tree.branch (129 : Fin 173) _
  apply congrArg (Tree.branch (129 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0056
  · rfl
  · rfl

def B0054 : Block := .branch 77 ![288230376151712129, 604462909808414098982402, 1461501637330902918203684832716283019655932549124, 174224571863678988303902555348386002788360, 11874700803313586210404939265819799534704452010000, 93536104789177807534223263433152627379965000024096, 23386880730812761739009834404490890679609888079936] ![(.leaf 0 (Common.fact 291).pointIds 291), B0055, (.leaf 2 (Common.fact 292).pointIds 292), (.leaf 3 (Common.fact 293).pointIds 293), (.leaf 4 (Common.fact 294).pointIds 294), (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 6 (Common.fact 296).pointIds 296)]
theorem treeEq0054 : B0054.tree = HexagonCover.NBand.M7100_7300.SplitData.node0054 := by
  change Tree.branch (77 : Fin 173) _ = Tree.branch (77 : Fin 173) _
  apply congrArg (Tree.branch (77 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0055
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0053 : Block := .branch 160 ![288230376151712129, 906694436769665430586882, 6148, 174224571863678988303902555348386002788360, 11874700803313586210404939265819799534704452010000, 93536104789177807534223263433152627379965000024096, 23386880730812761739009834404490890679609888079936] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), B0054, (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 290).pointIds 290)]
theorem treeEq0053 : B0053.tree = HexagonCover.NBand.M7100_7300.SplitData.node0053 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
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
theorem checked0053 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0053 (maskNeeds ![288230376151712129, 906694436769665430586882, 6148, 174224571863678988303902555348386002788360, 11874700803313586210404939265819799534704452010000, 93536104789177807534223263433152627379965000024096, 23386880730812761739009834404490890679609888079936]) := by
  rw [← treeEq0053]
  exact B0053.sound accepted0053
#print axioms checked0053

def Tip0033_0053 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0053 ![288230376151712129, 906694436769665430586882, 6148, 174224571863678988303902555348386002788360, 11874700803313586210404939265819799534704452010000, 93536104789177807534223263433152627379965000024096, 23386880730812761739009834404490890679609888079936] checked0053
def B0052 : Block := .branch 97 ![288230376151712129, 906694436769665430586882, 6148, 174224571863520531978874026673198914887688, 11874700803313586210404939265819799534704452010000, 93536104789177807534223263433152627379965000024096, 23386880730812761739009834404490890679609888079936] ![(.leaf 0 (Common.fact 279).pointIds 279), (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 281).pointIds 281), Tip0033_0053, (.leaf 4 (Common.fact 282).pointIds 282), (.leaf 5 (Common.fact 283).pointIds 283), (.leaf 6 (Common.fact 284).pointIds 284)]
theorem treeEq0052 : B0052.tree = HexagonCover.NBand.M7100_7300.SplitData.node0052 := by
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

def B0051 : Block := .branch 107 ![288230376151712129, 906694436769665430586882, 6148, 174224571863520531978874026673198914887688, 11874700803313586210404939265819799534704452010000, 93536104789177807534223263433152627379965000024096, 23386880730812761739009834404490890679609888079936] ![(.leaf 0 (Common.fact 273).pointIds 273), (.leaf 1 (Common.fact 274).pointIds 274), (.leaf 2 (Common.fact 275).pointIds 275), B0052, (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 278).pointIds 278)]
theorem treeEq0051 : B0051.tree = HexagonCover.NBand.M7100_7300.SplitData.node0051 := by
  change Tree.branch (107 : Fin 173) _ = Tree.branch (107 : Fin 173) _
  apply congrArg (Tree.branch (107 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0052
  · rfl
  · rfl
  · rfl

def B0050 : Block := .branch 118 ![288230376151712129, 906694436769665430586882, 6148, 174224571863520531978874026673198914887688, 11874700803313586210404939265819799534704452010000, 93536104789177807534223263433152627379965000024096, 23386880730812761739009834404490890679609888079936] ![(.leaf 0 (Common.fact 267).pointIds 267), (.leaf 1 (Common.fact 268).pointIds 268), (.leaf 2 (Common.fact 269).pointIds 269), B0051, (.leaf 4 (Common.fact 270).pointIds 270), (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 6 (Common.fact 272).pointIds 272)]
theorem treeEq0050 : B0050.tree = HexagonCover.NBand.M7100_7300.SplitData.node0050 := by
  change Tree.branch (118 : Fin 173) _ = Tree.branch (118 : Fin 173) _
  apply congrArg (Tree.branch (118 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0051
  · rfl
  · rfl
  · rfl

def B0049 : Block := .branch 128 ![288230376151712129, 906694436769665430586882, 6148, 174224571863520531978874026673198914887688, 11874700803313586210404939265819799534704452010000, 93536104789177807534223263433152627379965000024096, 23386880730812761739009834404490890679609888079936] ![(.leaf 0 (Common.fact 261).pointIds 261), (.leaf 1 (Common.fact 262).pointIds 262), (.leaf 2 (Common.fact 263).pointIds 263), B0050, (.leaf 4 (Common.fact 264).pointIds 264), (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 266).pointIds 266)]
theorem treeEq0049 : B0049.tree = HexagonCover.NBand.M7100_7300.SplitData.node0049 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0050
  · rfl
  · rfl
  · rfl

def B0048 : Block := .branch 137 ![288230376151712129, 906694436769665430586882, 6148, 38685626227668133590622216, 11874700803313586210404939265819799534704452010000, 93536104789177807534223263433152627379965000024096, 23386880730812761739009834404490890679609888079936] ![(.leaf 0 (Common.fact 256).pointIds 256), (.leaf 1 (Common.fact 257).pointIds 257), (.leaf 2 (Common.fact 258).pointIds 258), B0049, (.leaf 4 (Common.fact 259).pointIds 259), (.leaf 5 (Common.fact 260).pointIds 260), (.leaf 0 [] 0)]
theorem treeEq0048 : B0048.tree = HexagonCover.NBand.M7100_7300.SplitData.node0048 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0049
  · rfl
  · rfl
  · rfl

def B0047 : Block := .branch 151 ![288230376151712129, 906694436769665430586882, 6148, 38685626227668133590622216, 11874700803313586210404939265819799534704452010000, 93536104789177807534223263433152627379965000024096, 23384026235427349819247717832551991689337122586688] ![(.leaf 0 (Common.fact 250).pointIds 250), (.leaf 1 (Common.fact 251).pointIds 251), (.leaf 2 (Common.fact 252).pointIds 252), (.leaf 3 (Common.fact 253).pointIds 253), (.leaf 4 (Common.fact 254).pointIds 254), (.leaf 5 (Common.fact 255).pointIds 255), B0048]
theorem treeEq0047 : B0047.tree = HexagonCover.NBand.M7100_7300.SplitData.node0047 := by
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
  · exact treeEq0048

def B0046 : Block := .branch 163 ![288230376151712129, 906694436769665430586882, 6148, 38685626227668133590622216, 182687704666362864775460604089535377456991666192, 93536104789177807534223263433152627379965000024096, 23384026235427349819247717832551991689337122586688] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B0047, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 249).pointIds 249)]
theorem treeEq0046 : B0046.tree = HexagonCover.NBand.M7100_7300.SplitData.node0046 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0047
  · rfl
  · rfl

def B0045 : Block := .branch 113 ![288230376151712129, 906694436769665430586882, 6148, 38685626227668133590622216, 182687704666362864775460604089535377456991666192, 93536104789177807534223263433152627379965000024096, 23384026235427339434654000762896734628344464146496] ![(.leaf 0 (Common.fact 238).pointIds 238), (.leaf 1 (Common.fact 239).pointIds 239), (.leaf 2 (Common.fact 240).pointIds 240), (.leaf 3 (Common.fact 241).pointIds 241), (.leaf 4 (Common.fact 242).pointIds 242), (.leaf 5 (Common.fact 243).pointIds 243), B0046]
theorem treeEq0045 : B0045.tree = HexagonCover.NBand.M7100_7300.SplitData.node0045 := by
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
  · exact treeEq0046

def B0044 : Block := .branch 114 ![288230376151712129, 906694436769665430586882, 6148, 38685626227668133590622216, 182687704666362864775460604089535377456991666192, 93536104789177786765035829293842113257979683143712, 23384026235427339434654000762896734628344464146496] ![(.leaf 0 (Common.fact 232).pointIds 232), (.leaf 1 (Common.fact 233).pointIds 233), (.leaf 2 (Common.fact 234).pointIds 234), (.leaf 3 (Common.fact 235).pointIds 235), (.leaf 4 (Common.fact 236).pointIds 236), B0045, (.leaf 6 (Common.fact 237).pointIds 237)]
theorem treeEq0044 : B0044.tree = HexagonCover.NBand.M7100_7300.SplitData.node0044 := by
  change Tree.branch (114 : Fin 173) _ = Tree.branch (114 : Fin 173) _
  apply congrArg (Tree.branch (114 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0045
  · rfl

def B0043 : Block := .branch 159 ![288230376151712129, 906694436769665430586882, 6148, 38685626227668133590622216, 182687704666362864775460604089535377456991666192, 93536104789177786765035829293842113257979683143712, 23384026235427339434654000762896734628344464146496] ![(.leaf 0 (Common.fact 226).pointIds 226), (.leaf 1 (Common.fact 227).pointIds 227), (.leaf 2 (Common.fact 228).pointIds 228), (.leaf 3 (Common.fact 229).pointIds 229), (.leaf 4 (Common.fact 230).pointIds 230), (.leaf 5 (Common.fact 231).pointIds 231), B0044]
theorem treeEq0043 : B0043.tree = HexagonCover.NBand.M7100_7300.SplitData.node0043 := by
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
  · exact treeEq0044

def B0042 : Block := .branch 79 ![288230376151712129, 302231526962350843233794, 6148, 38685626227668133590622216, 182687704666362864775460604089535377456991666192, 93536104789177786765035829293842113257979683143712, 23384026235427339434654000762896734628344464146496] ![(.leaf 0 (Common.fact 220).pointIds 220), B0043, (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), (.leaf 5 (Common.fact 224).pointIds 224), (.leaf 6 (Common.fact 225).pointIds 225)]
theorem treeEq0042 : B0042.tree = HexagonCover.NBand.M7100_7300.SplitData.node0042 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0043
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0041 : Block := .branch 132 ![288230376151712129, 302231526962350843233794, 6148, 38685626227668133590622216, 182690840708656408144339882549917468632828444688, 93536104789177786765035829293842113257979683143712, 23384026229982821563918985347482740909436172763200] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 218).pointIds 218), (.leaf 5 (Common.fact 219).pointIds 219), B0042]
theorem treeEq0041 : B0041.tree = HexagonCover.NBand.M7100_7300.SplitData.node0041 := by
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
  · exact treeEq0042

def B0040 : Block := .branch 78 ![288230376151712129, 72058693549557250, 6148, 38685626227668133590622216, 182690840708656408144339882549917468632828444688, 93536104789177786765035829293842113257979683143712, 23384026229982821563918985347482740909436172763200] ![(.leaf 0 (Common.fact 140).pointIds 140), B0041, (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), (.leaf 4 (Common.fact 144).pointIds 144), (.leaf 5 (Common.fact 145).pointIds 145), (.leaf 6 (Common.fact 213).pointIds 213)]
theorem treeEq0040 : B0040.tree = HexagonCover.NBand.M7100_7300.SplitData.node0040 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0041
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0039 : Block := .branch 133 ![288230376151712129, 72058693549557250, 6148, 38685626227668133590622216, 182690840708656408144339882549917468632828444688, 93536104789177786765035829293842113257979683143712, 23384026219093785822448954516654753471619589996608] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), (.leaf 4 (Common.fact 211).pointIds 211), (.leaf 5 (Common.fact 212).pointIds 212), B0040]
theorem treeEq0039 : B0039.tree = HexagonCover.NBand.M7100_7300.SplitData.node0039 := by
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
  · exact treeEq0040

def B0038 : Block := .branch 157 ![288230376151712129, 72058693549557250, 6148, 38685626227668133590622216, 3136042293543368879278460382091175836876816, 93536104789177786765035829293842113257979683143712, 23384026219093785822448954516654753471619589996608] ![(.leaf 0 (Common.fact 202).pointIds 202), (.leaf 1 (Common.fact 203).pointIds 203), (.leaf 2 (Common.fact 204).pointIds 204), (.leaf 3 (Common.fact 205).pointIds 205), B0039, (.leaf 5 (Common.fact 206).pointIds 206), (.leaf 0 [] 0)]
theorem treeEq0038 : B0038.tree = HexagonCover.NBand.M7100_7300.SplitData.node0038 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0039
  · rfl
  · rfl

def B0037 : Block := .branch 166 ![288230376151712129, 72058693549557250, 6148, 38685626227668133590622216, 3136042293543368879278460382091175836876816, 393248, 23384026219093785822448954516654753471619589996608] ![(.leaf 0 (Common.fact 196).pointIds 196), (.leaf 1 (Common.fact 197).pointIds 197), (.leaf 2 (Common.fact 198).pointIds 198), (.leaf 3 (Common.fact 199).pointIds 199), (.leaf 4 (Common.fact 200).pointIds 200), B0038, (.leaf 6 (Common.fact 201).pointIds 201)]
theorem treeEq0037 : B0037.tree = HexagonCover.NBand.M7100_7300.SplitData.node0037 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0038
  · rfl

def B0036 : Block := .branch 87 ![288230376151712129, 72058693549557250, 36893488147419109380, 38685626227668133590622216, 3136042293543368879278460382091175836876816, 393248, 23384026219093785822448799774149842799085227606080] ![(.leaf 0 (Common.fact 128).pointIds 128), (.leaf 1 (Common.fact 129).pointIds 129), (.leaf 2 (Common.fact 130).pointIds 130), (.leaf 3 (Common.fact 131).pointIds 131), (.leaf 4 (Common.fact 132).pointIds 132), (.leaf 5 (Common.fact 133).pointIds 133), B0037]
theorem treeEq0036 : B0036.tree = HexagonCover.NBand.M7100_7300.SplitData.node0036 := by
  change Tree.branch (87 : Fin 173) _ = Tree.branch (87 : Fin 173) _
  apply congrArg (Tree.branch (87 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0037

def B0035 : Block := .branch 65 ![288230376151712129, 72058693549557250, 6148, 38685626227668133590622216, 3136042293543368879278460382091175836876816, 393248, 23384026219093785822448799774149842799085227606080] ![(.leaf 0 (Common.fact 122).pointIds 122), (.leaf 1 (Common.fact 123).pointIds 123), B0036, (.leaf 3 (Common.fact 124).pointIds 124), (.leaf 4 (Common.fact 125).pointIds 125), (.leaf 5 (Common.fact 126).pointIds 126), (.leaf 6 (Common.fact 195).pointIds 195)]
theorem treeEq0035 : B0035.tree = HexagonCover.NBand.M7100_7300.SplitData.node0035 := by
  change Tree.branch (65 : Fin 173) _ = Tree.branch (65 : Fin 173) _
  apply congrArg (Tree.branch (65 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0036
  · rfl
  · rfl
  · rfl
  · rfl

def B0034 : Block := .branch 138 ![288230376151712129, 72058693549557250, 6148, 38685626227668133590622216, 2787593149816327892691964784081045188345872, 393248, 23384026219093785822448799774149842799085227606080] ![(.leaf 0 (Common.fact 116).pointIds 116), (.leaf 1 (Common.fact 117).pointIds 117), (.leaf 2 (Common.fact 118).pointIds 118), (.leaf 3 (Common.fact 119).pointIds 119), B0035, (.leaf 5 (Common.fact 120).pointIds 120), (.leaf 6 (Common.fact 194).pointIds 194)]
theorem treeEq0034 : B0034.tree = HexagonCover.NBand.M7100_7300.SplitData.node0034 := by
  change Tree.branch (138 : Fin 173) _ = Tree.branch (138 : Fin 173) _
  apply congrArg (Tree.branch (138 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0035
  · rfl
  · rfl

def B0033 : Block := .branch 141 ![288230376151712129, 72058693549557250, 6148, 38685626227668133590622216, 98320, 393248, 23384026219093785822448799774149842799085227606080] ![(.leaf 0 (Common.fact 98).pointIds 98), (.leaf 1 (Common.fact 99).pointIds 99), (.leaf 2 (Common.fact 100).pointIds 100), (.leaf 3 (Common.fact 101).pointIds 101), B0034, (.leaf 5 (Common.fact 102).pointIds 102), (.leaf 6 (Common.fact 193).pointIds 193)]
theorem treeEq0033 : B0033.tree = HexagonCover.NBand.M7100_7300.SplitData.node0033 := by
  change Tree.branch (141 : Fin 173) _ = Tree.branch (141 : Fin 173) _
  apply congrArg (Tree.branch (141 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0034
  · rfl
  · rfl

theorem accepted0033 : B0033.accepted = true := by decide +kernel
theorem checked0033 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0033 (maskNeeds ![288230376151712129, 72058693549557250, 6148, 38685626227668133590622216, 98320, 393248, 23384026219093785822448799774149842799085227606080]) := by
  rw [← treeEq0033]
  exact B0033.sound accepted0033
#print axioms checked0033

def B0133 : Block := .branch 170 ![94266855607843243416434530245027883298303978242433, 1461501637330902918204303802735925710892893734402, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 58460065493236117052665946967078047569393322393616, 748288838313422294120286634350736906063837462396960, 2854517184751050952113765133124147397434802240] ![(.leaf 0 (Common.fact 485).pointIds 485), (.leaf 1 (Common.fact 486).pointIds 486), (.leaf 2 (Common.fact 487).pointIds 487), (.leaf 3 (Common.fact 488).pointIds 488), (.leaf 4 (Common.fact 489).pointIds 489), (.leaf 5 (Common.fact 490).pointIds 490), (.leaf 6 (Common.fact 491).pointIds 491)]
theorem treeEq0133 : B0133.tree = HexagonCover.NBand.M7100_7300.SplitData.node0133 := by
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

def B0134 : Block := .branch 170 ![93536104789177791958600338428897971189972715176321, 2192252455996354377305527249074424530583410443778, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 58460065493236117052665946967078047569393322393616, 748288838313422294120286634350736906063837462396960, 2854517184751050952113765133124147397434802240] ![(.leaf 0 (Common.fact 492).pointIds 492), (.leaf 1 (Common.fact 493).pointIds 493), (.leaf 2 (Common.fact 487).pointIds 487), (.leaf 3 (Common.fact 488).pointIds 488), (.leaf 4 (Common.fact 489).pointIds 489), (.leaf 5 (Common.fact 490).pointIds 490), (.leaf 6 (Common.fact 491).pointIds 491)]
theorem treeEq0134 : B0134.tree = HexagonCover.NBand.M7100_7300.SplitData.node0134 := by
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

def B0135 : Block := .branch 170 ![93536104789177791958600338428897971189972715176321, 1461501637330902918204303802735925710892893734402, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 58460065493236117052665946967078047569393322393616, 748288838313422294120286634350736906063837462396960, 733605335850202510053956181491265657225401073728] ![(.leaf 0 (Common.fact 492).pointIds 492), (.leaf 1 (Common.fact 486).pointIds 486), (.leaf 2 (Common.fact 487).pointIds 487), (.leaf 3 (Common.fact 488).pointIds 488), (.leaf 4 (Common.fact 489).pointIds 489), (.leaf 5 (Common.fact 490).pointIds 490), (.leaf 6 (Common.fact 494).pointIds 494)]
theorem treeEq0135 : B0135.tree = HexagonCover.NBand.M7100_7300.SplitData.node0135 := by
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

def B0132 : Block := .branch 159 ![93536104789177791958600338428897971189972715176321, 1461501637330902918204303802735925710892893734402, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 58460065493236117052665946967078047569393322393616, 748288838313422294120286634350736906063837462396960, 2854517184751050952113765133124147397434802240] ![B0133, B0134, (.leaf 2 (Common.fact 228).pointIds 228), (.leaf 3 (Common.fact 229).pointIds 229), (.leaf 4 (Common.fact 230).pointIds 230), (.leaf 5 (Common.fact 231).pointIds 231), B0135]
theorem treeEq0132 : B0132.tree = HexagonCover.NBand.M7100_7300.SplitData.node0132 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0133
  · exact treeEq0134
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0135

def B0136 : Block := .branch 170 ![5193564509135055857931993032425857, 1461501637330902918204303802735925710892893734402, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 58460065493236117052665946967078047569393322393616, 93536104789177786765035829293842113257979683143712, 2854517184751050952113765133124147397434802240] ![(.leaf 0 (Common.fact 495).pointIds 495), (.leaf 1 (Common.fact 486).pointIds 486), (.leaf 2 (Common.fact 487).pointIds 487), (.leaf 3 (Common.fact 488).pointIds 488), (.leaf 4 (Common.fact 489).pointIds 489), (.leaf 5 (Common.fact 496).pointIds 496), (.leaf 6 (Common.fact 491).pointIds 491)]
theorem treeEq0136 : B0136.tree = HexagonCover.NBand.M7100_7300.SplitData.node0136 := by
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

def B0131 : Block := .branch 166 ![5193564509135055857931993032425857, 1461501637330902918204303802735925710892893734402, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 58460065493236117052665946967078047569393322393616, 748288838313422294120286634350736906063837462396960, 2854517184751050952113765133124147397434802240] ![B0132, (.leaf 1 (Common.fact 197).pointIds 197), (.leaf 2 (Common.fact 198).pointIds 198), (.leaf 3 (Common.fact 199).pointIds 199), (.leaf 4 (Common.fact 200).pointIds 200), B0136, (.leaf 6 (Common.fact 444).pointIds 444)]
theorem treeEq0131 : B0131.tree = HexagonCover.NBand.M7100_7300.SplitData.node0131 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0132
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0136
  · rfl

def B0137 : Block := .branch 170 ![5193564509135055857931993032425857, 1461501637330902918204303802735925710892893734402, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 11874700803313586534923492924246526317860472586256, 795056890708011187502804548997657962692827303772192, 2854517184751050952113765133124147397434802240] ![(.leaf 0 (Common.fact 495).pointIds 495), (.leaf 1 (Common.fact 486).pointIds 486), (.leaf 2 (Common.fact 487).pointIds 487), (.leaf 3 (Common.fact 488).pointIds 488), (.leaf 4 (Common.fact 497).pointIds 497), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 491).pointIds 491)]
theorem treeEq0137 : B0137.tree = HexagonCover.NBand.M7100_7300.SplitData.node0137 := by
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

def B0130 : Block := .branch 165 ![5193564509135055857931993032425857, 1461501637330902918204303802735925710892893734402, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 11874700803313586534923492924246526317860472586256, 748288838313422294120286634350736906063837462396960, 2854517184751050952113765133124147397434802240] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), B0131, B0137, (.leaf 0 [] 0)]
theorem treeEq0130 : B0130.tree = HexagonCover.NBand.M7100_7300.SplitData.node0130 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0131
  · exact treeEq0137
  · rfl

def B0138 : Block := .branch 170 ![5193564509135055857931993032425857, 1461501637330902918204303802735925710892893734402, 2923003274661805836407369743351613006661011118084, 174224571863520570664500254341332505485320, 17720707352637197883219678596684931613328182181904, 748288838313422294120286634350736906063837462396960, 2854517184751050952113765133124147397434802240] ![(.leaf 0 (Common.fact 495).pointIds 495), (.leaf 1 (Common.fact 486).pointIds 486), (.leaf 2 (Common.fact 487).pointIds 487), (.leaf 3 (Common.fact 499).pointIds 499), (.leaf 4 (Common.fact 500).pointIds 500), (.leaf 5 (Common.fact 490).pointIds 490), (.leaf 6 (Common.fact 491).pointIds 491)]
theorem treeEq0138 : B0138.tree = HexagonCover.NBand.M7100_7300.SplitData.node0138 := by
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

def B0129 : Block := .branch 162 ![5193564509135055857931993032425857, 1461501637330902918204303802735925710892893734402, 2923003274661805836407369743351613006661011118084, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 748288838313422294120286634350736906063837462396960, 2860092371050683607899149062692309487811297344] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), B0130, B0138, (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq0129 : B0129.tree = HexagonCover.NBand.M7100_7300.SplitData.node0129 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0130
  · exact treeEq0138
  · rfl
  · rfl

def B0139 : Block := .branch 170 ![5193564509135055857931993032425857, 1461501637330902918204303802735925710892893734402, 77919046967349146032132, 2923003448886377699927862958680365044377189376008, 11874700803313586534923492924246526317860472586256, 748288838313422294120286634350736906063837462396960, 2854517184751050952113765133124147397434802240] ![(.leaf 0 (Common.fact 495).pointIds 495), (.leaf 1 (Common.fact 486).pointIds 486), (.leaf 2 (Common.fact 501).pointIds 501), (.leaf 3 (Common.fact 502).pointIds 502), (.leaf 4 (Common.fact 497).pointIds 497), (.leaf 5 (Common.fact 490).pointIds 490), (.leaf 6 (Common.fact 491).pointIds 491)]
theorem treeEq0139 : B0139.tree = HexagonCover.NBand.M7100_7300.SplitData.node0139 := by
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

def B0128 : Block := .branch 161 ![5193564509135055857931993032425857, 1461501637330902918204303802735925710892893734402, 77919046967349146032132, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 748288838313422294120286634350736906063837462396960, 2860092371050683607899149062692309487811297344] ![(.leaf 0 (Common.fact 331).pointIds 331), (.leaf 1 (Common.fact 332).pointIds 332), B0129, B0139, (.leaf 4 (Common.fact 333).pointIds 333), (.leaf 5 (Common.fact 334).pointIds 334), (.leaf 6 (Common.fact 457).pointIds 457)]
theorem treeEq0128 : B0128.tree = HexagonCover.NBand.M7100_7300.SplitData.node0128 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0129
  · exact treeEq0139
  · rfl
  · rfl
  · rfl

def B0140 : Block := .branch 170 ![5192298096474866913910771228344705, 1461501637330902918204303802735925710892893734402, 77919046967349146032132, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 748288838313422294120286634350736906063837462396960, 2854517184751052219764365361353548894138007616] ![(.leaf 0 (Common.fact 503).pointIds 503), (.leaf 1 (Common.fact 486).pointIds 486), (.leaf 2 (Common.fact 501).pointIds 501), (.leaf 3 (Common.fact 499).pointIds 499), (.leaf 4 (Common.fact 497).pointIds 497), (.leaf 5 (Common.fact 490).pointIds 490), (.leaf 6 (Common.fact 504).pointIds 504)]
theorem treeEq0140 : B0140.tree = HexagonCover.NBand.M7100_7300.SplitData.node0140 := by
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

def B0127 : Block := .branch 100 ![5192298096474866913910771228344705, 1461501637330902918204303802735925710892893734402, 77919046967349146032132, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 748288838313422294120286634350736906063837462396960, 2860092371050683607899149062692309487811297344] ![B0128, (.leaf 1 (Common.fact 452).pointIds 452), (.leaf 2 (Common.fact 453).pointIds 453), (.leaf 3 (Common.fact 454).pointIds 454), (.leaf 4 (Common.fact 455).pointIds 455), (.leaf 5 (Common.fact 456).pointIds 456), B0140]
theorem treeEq0127 : B0127.tree = HexagonCover.NBand.M7100_7300.SplitData.node0127 := by
  change Tree.branch (100 : Fin 173) _ = Tree.branch (100 : Fin 173) _
  apply congrArg (Tree.branch (100 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0128
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0140

def B0141 : Block := .branch 170 ![5192296859139290538337810916573569, 1461501637330902918204303802735925710892893734402, 77919046967349146032132, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 748288838313422294120286634350736906063837462396960, 2854517184751050953042220162588182603609145408] ![(.leaf 0 (Common.fact 505).pointIds 505), (.leaf 1 (Common.fact 486).pointIds 486), (.leaf 2 (Common.fact 501).pointIds 501), (.leaf 3 (Common.fact 499).pointIds 499), (.leaf 4 (Common.fact 497).pointIds 497), (.leaf 5 (Common.fact 490).pointIds 490), (.leaf 6 (Common.fact 506).pointIds 506)]
theorem treeEq0141 : B0141.tree = HexagonCover.NBand.M7100_7300.SplitData.node0141 := by
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

def B0126 : Block := .branch 90 ![5192296859139290538337810916573569, 1461501637330902918204303802735925710892893734402, 77919046967349146032132, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 748288838313422294120286634350736906063837462396960, 2860092371050683607899149062692309487811297344] ![B0127, (.leaf 1 (Common.fact 447).pointIds 447), (.leaf 2 (Common.fact 448).pointIds 448), (.leaf 3 (Common.fact 449).pointIds 449), (.leaf 4 (Common.fact 450).pointIds 450), (.leaf 5 (Common.fact 451).pointIds 451), B0141]
theorem treeEq0126 : B0126.tree = HexagonCover.NBand.M7100_7300.SplitData.node0126 := by
  change Tree.branch (90 : Fin 173) _ = Tree.branch (90 : Fin 173) _
  apply congrArg (Tree.branch (90 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0127
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0141

def B0142 : Block := .branch 170 ![5192296859139290538337810916573569, 618970019642691236961191426, 1461501637330902918203684835077466261090755155972, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 748288838313422294120286634350736906063837462396960, 2854517184751050952113765133124147397434802240] ![(.leaf 0 (Common.fact 505).pointIds 505), (.leaf 1 (Common.fact 507).pointIds 507), (.leaf 2 (Common.fact 508).pointIds 508), (.leaf 3 (Common.fact 499).pointIds 499), (.leaf 4 (Common.fact 497).pointIds 497), (.leaf 5 (Common.fact 490).pointIds 490), (.leaf 6 (Common.fact 491).pointIds 491)]
theorem treeEq0142 : B0142.tree = HexagonCover.NBand.M7100_7300.SplitData.node0142 := by
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

def B0125 : Block := .branch 160 ![5192296859139290538337810916573569, 618970019642691236961191426, 77919046967349146032132, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 748288838313422294120286634350736906063837462396960, 2860092371050683607899149062692309487811297344] ![(.leaf 0 (Common.fact 285).pointIds 285), B0126, B0142, (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 446).pointIds 446)]
theorem treeEq0125 : B0125.tree = HexagonCover.NBand.M7100_7300.SplitData.node0125 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0126
  · exact treeEq0142
  · rfl
  · rfl
  · rfl
  · rfl

def B0124 : Block := .branch 157 ![5192296859139290538337810916573569, 618970019642691236961191426, 77919046967349146032132, 174224571863520570664500254341332505485320, 11692013098647223670148032320156990940403481018384, 748288838313422294120286634350736906063837462396960, 2860092371050683607899149062692309487811297344] ![(.leaf 0 (Common.fact 202).pointIds 202), (.leaf 1 (Common.fact 203).pointIds 203), (.leaf 2 (Common.fact 204).pointIds 204), (.leaf 3 (Common.fact 205).pointIds 205), B0125, (.leaf 5 (Common.fact 484).pointIds 484), (.leaf 0 [] 0)]
theorem treeEq0124 : B0124.tree = HexagonCover.NBand.M7100_7300.SplitData.node0124 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0125
  · rfl
  · rfl

def B0123 : Block := .branch 169 ![5192296859139290538337810916573569, 618970019642691236961191426, 77919046967349146032132, 174224571863520570664500254341332505485320, 11693440346339929630029090606126440435539863765008, 393248, 2860092371050683607899149062692309487811297344] ![(.leaf 0 (Common.fact 481).pointIds 481), (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 473).pointIds 473), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 482).pointIds 482), B0124, (.leaf 6 (Common.fact 483).pointIds 483)]
theorem treeEq0123 : B0123.tree = HexagonCover.NBand.M7100_7300.SplitData.node0123 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0124
  · rfl

theorem accepted0123 : B0123.accepted = true := by decide +kernel
theorem checked0123 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0123 (maskNeeds ![5192296859139290538337810916573569, 618970019642691236961191426, 77919046967349146032132, 174224571863520570664500254341332505485320, 11693440346339929630029090606126440435539863765008, 393248, 2860092371050683607899149062692309487811297344]) := by
  rw [← treeEq0123]
  exact B0123.sound accepted0123
#print axioms checked0123

def Tip0104_0123 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0123 ![5192296859139290538337810916573569, 618970019642691236961191426, 77919046967349146032132, 174224571863520570664500254341332505485320, 11693440346339929630029090606126440435539863765008, 393248, 2860092371050683607899149062692309487811297344] checked0123
def B0114 : Block := .branch 169 ![94266855607843243416434530245027883298303978242433, 1461501637330902918204303802735925710892893734402, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 58460065493236117052665946967078047569393322393616, 2854495427947215627233879871820816201736912928, 16747358238029157353344982929643395798794304] ![(.leaf 0 (Common.fact 459).pointIds 459), (.leaf 1 (Common.fact 460).pointIds 460), (.leaf 2 (Common.fact 461).pointIds 461), (.leaf 3 (Common.fact 462).pointIds 462), (.leaf 4 (Common.fact 463).pointIds 463), (.leaf 5 (Common.fact 464).pointIds 464), (.leaf 6 (Common.fact 465).pointIds 465)]
theorem treeEq0114 : B0114.tree = HexagonCover.NBand.M7100_7300.SplitData.node0114 := by
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

def B0115 : Block := .branch 169 ![93536104789177791958600338428897971189972715176321, 2192252455996354377305527249074424530583410443778, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 58460065493236117052665946967078047569393322393616, 2854495427947215627233879871820816201736912928, 16747358238029157353344982929643395798794304] ![(.leaf 0 (Common.fact 466).pointIds 466), (.leaf 1 (Common.fact 467).pointIds 467), (.leaf 2 (Common.fact 461).pointIds 461), (.leaf 3 (Common.fact 462).pointIds 462), (.leaf 4 (Common.fact 463).pointIds 463), (.leaf 5 (Common.fact 464).pointIds 464), (.leaf 6 (Common.fact 465).pointIds 465)]
theorem treeEq0115 : B0115.tree = HexagonCover.NBand.M7100_7300.SplitData.node0115 := by
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

def B0116 : Block := .branch 169 ![93536104789177791958600338428897971189972715176321, 1461501637330902918204303802735925710892893734402, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 58460065493236117052665946967078047569393322393616, 2854495427947215627233879871820816201736912928, 730767566023689488259195761341071153223765065792] ![(.leaf 0 (Common.fact 466).pointIds 466), (.leaf 1 (Common.fact 460).pointIds 460), (.leaf 2 (Common.fact 461).pointIds 461), (.leaf 3 (Common.fact 462).pointIds 462), (.leaf 4 (Common.fact 463).pointIds 463), (.leaf 5 (Common.fact 464).pointIds 464), (.leaf 6 (Common.fact 468).pointIds 468)]
theorem treeEq0116 : B0116.tree = HexagonCover.NBand.M7100_7300.SplitData.node0116 := by
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

def B0113 : Block := .branch 159 ![93536104789177791958600338428897971189972715176321, 1461501637330902918204303802735925710892893734402, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 58460065493236117052665946967078047569393322393616, 2854495427947215627233879871820816201736912928, 16747358238029157353344982929643395798794304] ![B0114, B0115, (.leaf 2 (Common.fact 228).pointIds 228), (.leaf 3 (Common.fact 229).pointIds 229), (.leaf 4 (Common.fact 230).pointIds 230), (.leaf 5 (Common.fact 231).pointIds 231), B0116]
theorem treeEq0113 : B0113.tree = HexagonCover.NBand.M7100_7300.SplitData.node0113 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0114
  · exact treeEq0115
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0116

def B0117 : Block := .branch 169 ![93536104789177791958600338428897971189972715176321, 1461501637330902918204303802735925710892893734402, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 11874700803313586534923492924246526317860472586256, 46770906890016840598145148526792877445191578288160, 16747358238029157353344982929643395798794304] ![(.leaf 0 (Common.fact 466).pointIds 466), (.leaf 1 (Common.fact 460).pointIds 460), (.leaf 2 (Common.fact 461).pointIds 461), (.leaf 3 (Common.fact 462).pointIds 462), (.leaf 4 (Common.fact 469).pointIds 469), (.leaf 5 (Common.fact 470).pointIds 470), (.leaf 6 (Common.fact 465).pointIds 465)]
theorem treeEq0117 : B0117.tree = HexagonCover.NBand.M7100_7300.SplitData.node0117 := by
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

def B0112 : Block := .branch 165 ![93536104789177791958600338428897971189972715176321, 1461501637330902918204303802735925710892893734402, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 11874700803313586534923492924246526317860472586256, 2854495427947215627233879871820816201736912928, 16747358238029157353344982929643395798794304] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), B0113, B0117, (.leaf 0 [] 0)]
theorem treeEq0112 : B0112.tree = HexagonCover.NBand.M7100_7300.SplitData.node0112 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0113
  · exact treeEq0117
  · rfl

def B0118 : Block := .branch 169 ![93536104789177791958600338428897971189972715176321, 1461501637330902918204303802735925710892893734402, 2923003274661805836407369743351613006661011118084, 174224571863520570664500254341332505485320, 17720707352637197883219678596684931613328182181904, 2854495427947215627233879871820816201736912928, 16747358238029157353344982929643395798794304] ![(.leaf 0 (Common.fact 466).pointIds 466), (.leaf 1 (Common.fact 460).pointIds 460), (.leaf 2 (Common.fact 461).pointIds 461), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 464).pointIds 464), (.leaf 6 (Common.fact 465).pointIds 465)]
theorem treeEq0118 : B0118.tree = HexagonCover.NBand.M7100_7300.SplitData.node0118 := by
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

def B0111 : Block := .branch 162 ![93536104789177791958600338428897971189972715176321, 1461501637330902918204303802735925710892893734402, 2923003274661805836407369743351613006661011118084, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 2854495427947215627233879871820816201736912928, 16747358238029157353344982929643395798794304] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), B0112, B0118, (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq0111 : B0111.tree = HexagonCover.NBand.M7100_7300.SplitData.node0111 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0112
  · exact treeEq0118
  · rfl
  · rfl

def B0119 : Block := .branch 169 ![93536104789177791958600338428897971189972715176321, 1461501637330902918204303802735925710892893734402, 77919046967349146032132, 2923003448886377699927862958680365044377189376008, 11874700803313586534923492924246526317860472586256, 2854495427947215627233879871820816201736912928, 16747358238029157353344982929643395798794304] ![(.leaf 0 (Common.fact 466).pointIds 466), (.leaf 1 (Common.fact 460).pointIds 460), (.leaf 2 (Common.fact 473).pointIds 473), (.leaf 3 (Common.fact 474).pointIds 474), (.leaf 4 (Common.fact 469).pointIds 469), (.leaf 5 (Common.fact 464).pointIds 464), (.leaf 6 (Common.fact 465).pointIds 465)]
theorem treeEq0119 : B0119.tree = HexagonCover.NBand.M7100_7300.SplitData.node0119 := by
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

def B0110 : Block := .branch 161 ![93536104789177791958600338428897971189972715176321, 1461501637330902918204303802735925710892893734402, 77919046967349146032132, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 2854495427947215627233879871820816201736912928, 16747358238029157353344982929643395798794304] ![(.leaf 0 (Common.fact 331).pointIds 331), (.leaf 1 (Common.fact 332).pointIds 332), B0111, B0119, (.leaf 4 (Common.fact 333).pointIds 333), (.leaf 5 (Common.fact 334).pointIds 334), (.leaf 6 (Common.fact 457).pointIds 457)]
theorem treeEq0110 : B0110.tree = HexagonCover.NBand.M7100_7300.SplitData.node0110 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0111
  · exact treeEq0119
  · rfl
  · rfl
  · rfl

def B0120 : Block := .branch 169 ![93536104789177791957333925768709027168750911095169, 1461501637330902918204303802735925710892893734402, 77919046967349146032132, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 2854495427947215627233879871820816201736912928, 16747358238030425003945211159044892501999680] ![(.leaf 0 (Common.fact 475).pointIds 475), (.leaf 1 (Common.fact 460).pointIds 460), (.leaf 2 (Common.fact 473).pointIds 473), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 469).pointIds 469), (.leaf 5 (Common.fact 464).pointIds 464), (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq0120 : B0120.tree = HexagonCover.NBand.M7100_7300.SplitData.node0120 := by
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

def B0109 : Block := .branch 100 ![93536104789177791957333925768709027168750911095169, 1461501637330902918204303802735925710892893734402, 77919046967349146032132, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 2854495427947215627233879871820816201736912928, 16747358238029157353344982929643395798794304] ![B0110, (.leaf 1 (Common.fact 452).pointIds 452), (.leaf 2 (Common.fact 453).pointIds 453), (.leaf 3 (Common.fact 454).pointIds 454), (.leaf 4 (Common.fact 455).pointIds 455), (.leaf 5 (Common.fact 456).pointIds 456), B0120]
theorem treeEq0109 : B0109.tree = HexagonCover.NBand.M7100_7300.SplitData.node0109 := by
  change Tree.branch (100 : Fin 173) _ = Tree.branch (100 : Fin 173) _
  apply congrArg (Tree.branch (100 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0110
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0120

def B0121 : Block := .branch 169 ![93536104789177791957332688433132651595790599324033, 1461501637330902918204303802735925710892893734402, 77919046967349146032132, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 2854495427947215627233879871820816201736912928, 16747358238029158281800012393678601973137472] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 460).pointIds 460), (.leaf 2 (Common.fact 473).pointIds 473), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 469).pointIds 469), (.leaf 5 (Common.fact 464).pointIds 464), (.leaf 6 (Common.fact 478).pointIds 478)]
theorem treeEq0121 : B0121.tree = HexagonCover.NBand.M7100_7300.SplitData.node0121 := by
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

def B0108 : Block := .branch 90 ![93536104789177791957332688433132651595790599324033, 1461501637330902918204303802735925710892893734402, 77919046967349146032132, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 2854495427947215627233879871820816201736912928, 16747358238029157353344982929643395798794304] ![B0109, (.leaf 1 (Common.fact 447).pointIds 447), (.leaf 2 (Common.fact 448).pointIds 448), (.leaf 3 (Common.fact 449).pointIds 449), (.leaf 4 (Common.fact 450).pointIds 450), (.leaf 5 (Common.fact 451).pointIds 451), B0121]
theorem treeEq0108 : B0108.tree = HexagonCover.NBand.M7100_7300.SplitData.node0108 := by
  change Tree.branch (90 : Fin 173) _ = Tree.branch (90 : Fin 173) _
  apply congrArg (Tree.branch (90 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0109
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0121

def B0122 : Block := .branch 169 ![93536104789177791957332688433132651595790599324033, 618970019642691236961191426, 1461501637330902918203684835077466261090755155972, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 2854495427947215627233879871820816201736912928, 16747358238029157353344982929643395798794304] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 469).pointIds 469), (.leaf 5 (Common.fact 464).pointIds 464), (.leaf 6 (Common.fact 465).pointIds 465)]
theorem treeEq0122 : B0122.tree = HexagonCover.NBand.M7100_7300.SplitData.node0122 := by
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

def B0107 : Block := .branch 160 ![93536104789177791957332688433132651595790599324033, 618970019642691236961191426, 77919046967349146032132, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 2854495427947215627233879871820816201736912928, 16747358238029157353344982929643395798794304] ![(.leaf 0 (Common.fact 285).pointIds 285), B0108, B0122, (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 446).pointIds 446)]
theorem treeEq0107 : B0107.tree = HexagonCover.NBand.M7100_7300.SplitData.node0107 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0108
  · exact treeEq0122
  · rfl
  · rfl
  · rfl
  · rfl

def B0106 : Block := .branch 157 ![93536104789177791957332688433132651595790599324033, 618970019642691236961191426, 77919046967349146032132, 174224571863520570664500254341332505485320, 11692013098647223670148032320156990940403481018384, 2854495427947215627233879871820816201736912928, 16747358238029157353344982929643395798794304] ![(.leaf 0 (Common.fact 202).pointIds 202), (.leaf 1 (Common.fact 203).pointIds 203), (.leaf 2 (Common.fact 204).pointIds 204), (.leaf 3 (Common.fact 205).pointIds 205), B0107, (.leaf 5 (Common.fact 445).pointIds 445), (.leaf 0 [] 0)]
theorem treeEq0106 : B0106.tree = HexagonCover.NBand.M7100_7300.SplitData.node0106 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0107
  · rfl
  · rfl

def B0105 : Block := .branch 166 ![5192296859139290538337810916573569, 618970019642691236961191426, 77919046967349146032132, 174224571863520570664500254341332505485320, 11692013098647223670148032320156990940403481018384, 2854495427947215627233879871820816201736912928, 16747358238029157353344982929643395798794304] ![B0106, (.leaf 1 (Common.fact 197).pointIds 197), (.leaf 2 (Common.fact 198).pointIds 198), (.leaf 3 (Common.fact 199).pointIds 199), (.leaf 4 (Common.fact 200).pointIds 200), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 444).pointIds 444)]
theorem treeEq0105 : B0105.tree = HexagonCover.NBand.M7100_7300.SplitData.node0105 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0106
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0104 : Block := .branch 151 ![5192296859139290538337810916573569, 618970019642691236961191426, 77919046967349146032132, 174224571863520570664500254341332505485320, 11693440346339929630029090606126440435539863765008, 42535295865117307932921825928971419680, 16747358238029157353344982929643395798794304] ![(.leaf 0 (Common.fact 250).pointIds 250), (.leaf 1 (Common.fact 251).pointIds 251), (.leaf 2 (Common.fact 252).pointIds 252), (.leaf 3 (Common.fact 253).pointIds 253), (.leaf 4 (Common.fact 442).pointIds 442), B0105, Tip0104_0123]
theorem treeEq0104 : B0104.tree = HexagonCover.NBand.M7100_7300.SplitData.node0104 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0105
  · rfl

theorem accepted0104 : B0104.accepted = true := by decide +kernel
theorem checked0104 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0104 (maskNeeds ![5192296859139290538337810916573569, 618970019642691236961191426, 77919046967349146032132, 174224571863520570664500254341332505485320, 11693440346339929630029090606126440435539863765008, 42535295865117307932921825928971419680, 16747358238029157353344982929643395798794304]) := by
  rw [← treeEq0104]
  exact B0104.sound accepted0104
#print axioms checked0104

end HexagonCover.NBand.M7100_7300.SplitTree.Run0000
