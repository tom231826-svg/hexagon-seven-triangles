import HexagonCover.NBand.M6700_6900.SplitData
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6700_6900.SplitTree.Run0000
open OwnerTree HexagonCover.NBand.M6700_6900

abbrev Block := Chunk (n := 175) (Certificate := Fin 929) (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck

def B0069 : Block := .branch 168 ![20769187434139311955273866075439489, 1856910058928071511860315650, 4384504911992708754611054500510032300402620241924, 5846006723548183536335309995365386419956235657224, 58460065493236117052665946967078047569393322393616, 10384593717069655257060992658833440, 2854517184751053487414965589582950390841212992] ![(.leaf 0 (Common.fact 362).pointIds 362), (.leaf 1 (Common.fact 363).pointIds 363), (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), (.leaf 6 (Common.fact 368).pointIds 368)]
theorem treeEq0069 : B0069.tree = HexagonCover.NBand.M6700_6900.SplitData.node0069 := by
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

def B0070 : Block := .branch 168 ![20769187434139311955273866075439489, 1856910058928071511860315650, 4384504911992708754611054500510032300402620241924, 174224571863520570664500254341332505485320, 52614058943912505055332653977786188707613571645456, 10384593717069655257060992658833440, 2854517184751053487414965589582950390841212992] ![(.leaf 0 (Common.fact 362).pointIds 362), (.leaf 1 (Common.fact 363).pointIds 363), (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 369).pointIds 369), (.leaf 4 (Common.fact 370).pointIds 370), (.leaf 5 (Common.fact 367).pointIds 367), (.leaf 6 (Common.fact 368).pointIds 368)]
theorem treeEq0070 : B0070.tree = HexagonCover.NBand.M6700_6900.SplitData.node0070 := by
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

def B0068 : Block := .branch 162 ![20769187434139311955273866075439489, 1856910058928071511860315650, 4384504911992708754611054500510032300402620241924, 174224571863520570664500254341332505485320, 58460065493236117052665946967078047569393322393616, 10384593717069655257060992658833440, 2854517187409509478984797335390564511401902144] ![(.leaf 0 (Common.fact 357).pointIds 357), (.leaf 1 (Common.fact 358).pointIds 358), (.leaf 2 (Common.fact 359).pointIds 359), B0069, B0070, (.leaf 5 (Common.fact 360).pointIds 360), (.leaf 6 (Common.fact 361).pointIds 361)]
theorem treeEq0068 : B0068.tree = HexagonCover.NBand.M6700_6900.SplitData.node0068 := by
  change Tree.branch (162 : Fin 175) _ = Tree.branch (162 : Fin 175) _
  apply congrArg (Tree.branch (162 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0069
  · exact treeEq0070
  · rfl
  · rfl

def B0071 : Block := .branch 168 ![20769187434139311955273866075439489, 1856910058928071511860315650, 1461501637330902918203684835077466261090755155972, 2923003448886377699927862958680365044377189376008, 58460065493236117052665946967078047569393322393616, 10384593717069655257060992658833440, 2854517184751053487414965589582950390841212992] ![(.leaf 0 (Common.fact 362).pointIds 362), (.leaf 1 (Common.fact 363).pointIds 363), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), (.leaf 6 (Common.fact 368).pointIds 368)]
theorem treeEq0071 : B0071.tree = HexagonCover.NBand.M6700_6900.SplitData.node0071 := by
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

def B0067 : Block := .branch 161 ![20769187434139311955273866075439489, 1856910058928071511860315650, 1461501637330902918203684835077466261090755155972, 174224571863520570664500254341332505485320, 58460065493236117052665946967078047569393322393616, 10384593717069655257060992658833440, 2854517187409509478984797335390564511401902144] ![(.leaf 0 (Common.fact 352).pointIds 352), (.leaf 1 (Common.fact 353).pointIds 353), B0068, B0071, (.leaf 4 (Common.fact 354).pointIds 354), (.leaf 5 (Common.fact 355).pointIds 355), (.leaf 6 (Common.fact 356).pointIds 356)]
theorem treeEq0067 : B0067.tree = HexagonCover.NBand.M6700_6900.SplitData.node0067 := by
  change Tree.branch (161 : Fin 175) _ = Tree.branch (161 : Fin 175) _
  apply congrArg (Tree.branch (161 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0068
  · exact treeEq0071
  · rfl
  · rfl
  · rfl

def B0072 : Block := .branch 168 ![2475880080011912430556807553, 1856910058928071511860315650, 1461501637330902918203684835077466261090755155972, 174224571863520570664500254341332505485320, 58460065493236117052665946967078047569393322393616, 31153781151208965771182977975713824, 2854517184751053487414965589582950390841212992] ![(.leaf 0 (Common.fact 373).pointIds 373), (.leaf 1 (Common.fact 363).pointIds 363), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 369).pointIds 369), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 368).pointIds 368)]
theorem treeEq0072 : B0072.tree = HexagonCover.NBand.M6700_6900.SplitData.node0072 := by
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

def B0066 : Block := .branch 114 ![2475880080011912430556807553, 1856910058928071511860315650, 1461501637330902918203684835077466261090755155972, 174224571863520570664500254341332505485320, 58460065493236117052665946967078047569393322393616, 10384593717069655257060992658833440, 2854517187409509478984797335390564511401902144] ![B0067, (.leaf 1 (Common.fact 347).pointIds 347), (.leaf 2 (Common.fact 348).pointIds 348), (.leaf 3 (Common.fact 349).pointIds 349), (.leaf 4 (Common.fact 350).pointIds 350), B0072, (.leaf 6 (Common.fact 351).pointIds 351)]
theorem treeEq0066 : B0066.tree = HexagonCover.NBand.M6700_6900.SplitData.node0066 := by
  change Tree.branch (114 : Fin 175) _ = Tree.branch (114 : Fin 175) _
  apply congrArg (Tree.branch (114 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0067
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0072
  · rfl

def B0065 : Block := .branch 165 ![2475880080011912430556807553, 1856910058928071511860315650, 1461501637330902918203684835077466261090755155972, 174224571863520570664500254341332505485320, 11692013098647223670148032320156990940403481018384, 10384593717069655257060992658833440, 2854517187409509478984797335390564511401902144] ![(.leaf 0 (Common.fact 342).pointIds 342), (.leaf 1 (Common.fact 343).pointIds 343), (.leaf 2 (Common.fact 344).pointIds 344), (.leaf 3 (Common.fact 345).pointIds 345), B0066, (.leaf 5 (Common.fact 346).pointIds 346), (.leaf 0 [] 0)]
theorem treeEq0065 : B0065.tree = HexagonCover.NBand.M6700_6900.SplitData.node0065 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0066
  · rfl
  · rfl

def B0064 : Block := .branch 167 ![2475880080011912430556807553, 1856910058928071511860315650, 1461501637330902918203684835077466261090755155972, 174224571863520570664500254341332505485320, 11692013098647223670148032320156990940403481018384, 10384593717069655257060992658833440, 2854517187409509478984797335390564511401902144] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 339).pointIds 339), B0065, (.leaf 5 (Common.fact 340).pointIds 340), (.leaf 6 (Common.fact 341).pointIds 341)]
theorem treeEq0064 : B0064.tree = HexagonCover.NBand.M6700_6900.SplitData.node0064 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0065
  · rfl
  · rfl

def B0073 : Block := .branch 168 ![2475880080011912430556807553, 1856910058928071511860315650, 1461501637330902918203684835077466261090755155972, 174224571863520570664500254341332505485320, 11693440346339929630029090606126440435539863765008, 93536104789177786765035829293842113257979683143712, 2854517163493790148573381278379098419014139968] ![(.leaf 0 (Common.fact 373).pointIds 373), (.leaf 1 (Common.fact 363).pointIds 363), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 369).pointIds 369), (.leaf 4 (Common.fact 375).pointIds 375), (.leaf 5 (Common.fact 376).pointIds 376), (.leaf 6 (Common.fact 377).pointIds 377)]
theorem treeEq0073 : B0073.tree = HexagonCover.NBand.M6700_6900.SplitData.node0073 := by
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

def B0063 : Block := .branch 113 ![2475880080011912430556807553, 1856910058928071511860315650, 1461501637330902918203684835077466261090755155972, 174224571863520570664500254341332505485320, 11693440346339929630029090606126440435539863765008, 93536104789177786765035829293842113257979683143712, 2854517187409509478984797335390564511401902144] ![(.leaf 0 (Common.fact 331).pointIds 331), (.leaf 1 (Common.fact 332).pointIds 332), (.leaf 2 (Common.fact 333).pointIds 333), (.leaf 3 (Common.fact 334).pointIds 334), (.leaf 4 (Common.fact 335).pointIds 335), B0064, B0073]
theorem treeEq0063 : B0063.tree = HexagonCover.NBand.M6700_6900.SplitData.node0063 := by
  change Tree.branch (113 : Fin 175) _ = Tree.branch (113 : Fin 175) _
  apply congrArg (Tree.branch (113 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0064
  · exact treeEq0073

def B0074 : Block := .branch 168 ![604464350959195345912193, 1856910058928071511860315650, 1461501637330902918203684835077466261090755155972, 174224571863520570664500254341332505485320, 11693440346339929630029090606126440435539863765008, 93536104789177786765035829293842113257979683143712, 2854517184751050954280160201873562878508269632] ![(.leaf 0 (Common.fact 378).pointIds 378), (.leaf 1 (Common.fact 363).pointIds 363), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 369).pointIds 369), (.leaf 4 (Common.fact 375).pointIds 375), (.leaf 5 (Common.fact 376).pointIds 376), (.leaf 6 (Common.fact 379).pointIds 379)]
theorem treeEq0074 : B0074.tree = HexagonCover.NBand.M6700_6900.SplitData.node0074 := by
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

def B0062 : Block := .branch 91 ![604464350959195345912193, 1856910058928071511860315650, 1461501637330902918203684835077466261090755155972, 174224571863520570664500254341332505485320, 11693440346339929630029090606126440435539863765008, 93536104789177786765035829293842113257979683143712, 2854517187409509478984797335390564511401902144] ![B0063, (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 329).pointIds 329), (.leaf 5 (Common.fact 330).pointIds 330), B0074]
theorem treeEq0062 : B0062.tree = HexagonCover.NBand.M6700_6900.SplitData.node0062 := by
  change Tree.branch (91 : Fin 175) _ = Tree.branch (91 : Fin 175) _
  apply congrArg (Tree.branch (91 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0063
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0074

def B0061 : Block := .branch 160 ![604464350959195345912193, 1856910058928071511860315650, 2361183241434822612996, 174224571863520570664500254341332505485320, 11693440346339929630029090606126440435539863765008, 93536104789177786765035829293842113257979683143712, 2854517187409509478984797335390564511401902144] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), B0062, (.leaf 3 (Common.fact 322).pointIds 322), (.leaf 4 (Common.fact 323).pointIds 323), (.leaf 5 (Common.fact 324).pointIds 324), (.leaf 6 (Common.fact 325).pointIds 325)]
theorem treeEq0061 : B0061.tree = HexagonCover.NBand.M6700_6900.SplitData.node0061 := by
  change Tree.branch (160 : Fin 175) _ = Tree.branch (160 : Fin 175) _
  apply congrArg (Tree.branch (160 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0062
  · rfl
  · rfl
  · rfl
  · rfl

def B0075 : Block := .branch 168 ![604464350959195345912193, 618970019642691236961191426, 77919046967349146032132, 174224571863520570664500254341332505485320, 11693440346339929630029090606126440435539863765008, 93536104789177786765035829293842113257979683143712, 2854517184751053488343420619046985597015556160] ![(.leaf 0 (Common.fact 378).pointIds 378), (.leaf 1 (Common.fact 380).pointIds 380), (.leaf 2 (Common.fact 381).pointIds 381), (.leaf 3 (Common.fact 369).pointIds 369), (.leaf 4 (Common.fact 375).pointIds 375), (.leaf 5 (Common.fact 376).pointIds 376), (.leaf 6 (Common.fact 382).pointIds 382)]
theorem treeEq0075 : B0075.tree = HexagonCover.NBand.M6700_6900.SplitData.node0075 := by
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

def B0060 : Block := .branch 90 ![604464350959195345912193, 618970019642691236961191426, 77919046967349146032132, 174224571863520570664500254341332505485320, 11693440346339929630029090606126440435539863765008, 93536104789177786765035829293842113257979683143712, 2854517187409509478984797335390564511401902144] ![(.leaf 0 (Common.fact 315).pointIds 315), B0061, (.leaf 2 (Common.fact 316).pointIds 316), (.leaf 3 (Common.fact 317).pointIds 317), (.leaf 4 (Common.fact 318).pointIds 318), (.leaf 5 (Common.fact 319).pointIds 319), B0075]
theorem treeEq0060 : B0060.tree = HexagonCover.NBand.M6700_6900.SplitData.node0060 := by
  change Tree.branch (90 : Fin 175) _ = Tree.branch (90 : Fin 175) _
  apply congrArg (Tree.branch (90 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0061
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0075

def B0076 : Block := .branch 168 ![604464350959195345912193, 453347182356585452144130, 77919046967349146032132, 174224571863520570664500254341332505485320, 11693440346339929630029090606126440435539863765008, 93536104789177786765035829293842113257979683143712, 2854517184751053487724450599404295459565994048] ![(.leaf 0 (Common.fact 378).pointIds 378), (.leaf 1 (Common.fact 383).pointIds 383), (.leaf 2 (Common.fact 381).pointIds 381), (.leaf 3 (Common.fact 369).pointIds 369), (.leaf 4 (Common.fact 375).pointIds 375), (.leaf 5 (Common.fact 376).pointIds 376), (.leaf 6 (Common.fact 384).pointIds 384)]
theorem treeEq0076 : B0076.tree = HexagonCover.NBand.M6700_6900.SplitData.node0076 := by
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

def B0059 : Block := .branch 89 ![604464350959195345912193, 453347182356585452144130, 77919046967349146032132, 174224571863520570664500254341332505485320, 11693440346339929630029090606126440435539863765008, 93536104789177786765035829293842113257979683143712, 2854517187409509478984797335390564511401902144] ![(.leaf 0 (Common.fact 98).pointIds 98), B0060, (.leaf 2 (Common.fact 100).pointIds 100), (.leaf 3 (Common.fact 101).pointIds 101), (.leaf 4 (Common.fact 102).pointIds 102), (.leaf 5 (Common.fact 103).pointIds 103), B0076]
theorem treeEq0059 : B0059.tree = HexagonCover.NBand.M6700_6900.SplitData.node0059 := by
  change Tree.branch (89 : Fin 175) _ = Tree.branch (89 : Fin 175) _
  apply congrArg (Tree.branch (89 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0060
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0076

def B0077 : Block := .branch 168 ![604464350959195345912193, 453347182356585452144130, 77919046967349146032132, 174224571863678988303902555348386002788360, 11693440346339929630029090606126440435539863765008, 93536104789177786765035829293842113257979683143712, 2854517184751053170424944280070263749484216384] ![(.leaf 0 (Common.fact 378).pointIds 378), (.leaf 1 (Common.fact 383).pointIds 383), (.leaf 2 (Common.fact 381).pointIds 381), (.leaf 3 (Common.fact 385).pointIds 385), (.leaf 4 (Common.fact 375).pointIds 375), (.leaf 5 (Common.fact 376).pointIds 376), (.leaf 6 (Common.fact 386).pointIds 386)]
theorem treeEq0077 : B0077.tree = HexagonCover.NBand.M6700_6900.SplitData.node0077 := by
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

def B0058 : Block := .branch 86 ![604464350959195345912193, 453347182356585452144130, 77919046967349146032132, 174224571863678988303902555348386002788360, 11693440346339929630029090606126440435539863765008, 93536104789177786765035829293842113257979683143712, 2854517187409509478984797335390564511401902144] ![(.leaf 0 (Common.fact 310).pointIds 310), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), B0059, (.leaf 4 (Common.fact 313).pointIds 313), (.leaf 5 (Common.fact 314).pointIds 314), B0077]
theorem treeEq0058 : B0058.tree = HexagonCover.NBand.M6700_6900.SplitData.node0058 := by
  change Tree.branch (86 : Fin 175) _ = Tree.branch (86 : Fin 175) _
  apply congrArg (Tree.branch (86 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0059
  · rfl
  · rfl
  · exact treeEq0077

theorem accepted0058 : B0058.accepted = true := by decide +kernel
theorem checked0058 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6700_6900.SplitData.node0058 (maskNeeds ![604464350959195345912193, 453347182356585452144130, 77919046967349146032132, 174224571863678988303902555348386002788360, 11693440346339929630029090606126440435539863765008, 93536104789177786765035829293842113257979683143712, 2854517187409509478984797335390564511401902144]) := by
  rw [← treeEq0058]
  exact B0058.sound accepted0058
#print axioms checked0058

def Tip0055_0058 : Block := .tip HexagonCover.NBand.M6700_6900.SplitData.node0058 ![604464350959195345912193, 453347182356585452144130, 77919046967349146032132, 174224571863678988303902555348386002788360, 11693440346339929630029090606126440435539863765008, 93536104789177786765035829293842113257979683143712, 2854517187409509478984797335390564511401902144] checked0058
def B0079 : Block := .branch 168 ![1441151880758559105, 755578637260242745820674, 1461501637330902918203684835077466261090755155972, 174224571863678988303902555348386002788360, 11693440346339929630029090606126440435539863765008, 93536104789177786765035829293842113257979683143712, 2854517184751053487414965589582950390841212992] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 385).pointIds 385), (.leaf 4 (Common.fact 375).pointIds 375), (.leaf 5 (Common.fact 376).pointIds 376), (.leaf 6 (Common.fact 368).pointIds 368)]
theorem treeEq0079 : B0079.tree = HexagonCover.NBand.M6700_6900.SplitData.node0079 := by
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

def B0078 : Block := .branch 160 ![1441151880758559105, 755578637260242745820674, 2361183241434822612996, 174224571863678988303902555348386002788360, 11693440346339929630029090606126440435539863765008, 93536104789177786765035829293842113257979683143712, 2854517187409509478984797335390564511401902144] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 387).pointIds 387), B0079, (.leaf 3 (Common.fact 322).pointIds 322), (.leaf 4 (Common.fact 323).pointIds 323), (.leaf 5 (Common.fact 324).pointIds 324), (.leaf 6 (Common.fact 325).pointIds 325)]
theorem treeEq0078 : B0078.tree = HexagonCover.NBand.M6700_6900.SplitData.node0078 := by
  change Tree.branch (160 : Fin 175) _ = Tree.branch (160 : Fin 175) _
  apply congrArg (Tree.branch (160 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0079
  · rfl
  · rfl
  · rfl
  · rfl

def B0057 : Block := .branch 79 ![1441151880758559105, 453347182356585452144130, 77919046967349146032132, 174224571863678988303902555348386002788360, 11693440346339929630029090606126440435539863765008, 93536104789177786765035829293842113257979683143712, 2854517187409509478984797335390564511401902144] ![Tip0055_0058, B0078, (.leaf 2 (Common.fact 305).pointIds 305), (.leaf 3 (Common.fact 306).pointIds 306), (.leaf 4 (Common.fact 307).pointIds 307), (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 309).pointIds 309)]
theorem treeEq0057 : B0057.tree = HexagonCover.NBand.M6700_6900.SplitData.node0057 := by
  change Tree.branch (79 : Fin 175) _ = Tree.branch (79 : Fin 175) _
  apply congrArg (Tree.branch (79 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0078
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0084 : Block := .branch 168 ![604464350959195345912193, 1461501637330902918203685134947737924412737848834, 153476910693263469451268, 2923003448886377699927862958680365044377189376008, 11693440346339929630029090606126440435539863765008, 93536104789177786765035829293842113257979683143712, 2854517184751053488343420619046985597015556160] ![(.leaf 0 (Common.fact 378).pointIds 378), (.leaf 1 (Common.fact 394).pointIds 394), (.leaf 2 (Common.fact 395).pointIds 395), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 375).pointIds 375), (.leaf 5 (Common.fact 376).pointIds 376), (.leaf 6 (Common.fact 382).pointIds 382)]
theorem treeEq0084 : B0084.tree = HexagonCover.NBand.M6700_6900.SplitData.node0084 := by
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

def B0083 : Block := .branch 79 ![1441151880758559105, 1461501637330902918203685134947737924412737848834, 153476910693263469451268, 2923003448886377699927862958680365044377189376008, 11693440346339929630029090606126440435539863765008, 93536104789177786765035829293842113257979683143712, 2854517187409509480222737374675944786301026368] ![B0084, (.leaf 1 (Common.fact 393).pointIds 393), (.leaf 2 (Common.fact 305).pointIds 305), (.leaf 3 (Common.fact 306).pointIds 306), (.leaf 4 (Common.fact 307).pointIds 307), (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 309).pointIds 309)]
theorem treeEq0083 : B0083.tree = HexagonCover.NBand.M6700_6900.SplitData.node0083 := by
  change Tree.branch (79 : Fin 175) _ = Tree.branch (79 : Fin 175) _
  apply congrArg (Tree.branch (79 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0084
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0082 : Block := .branch 90 ![1441151880758559105, 1461501637330902918203685134947737924412737848834, 153476910693263469451268, 2923003448886377699927862958680365044377189376008, 11693440346339929630029090606126440435539863765008, 93536104789177786765035829293842113257979683143712, 2854517187409509478984797335390564511401902144] ![(.leaf 0 (Common.fact 315).pointIds 315), (.leaf 1 (Common.fact 392).pointIds 392), (.leaf 2 (Common.fact 316).pointIds 316), (.leaf 3 (Common.fact 317).pointIds 317), (.leaf 4 (Common.fact 318).pointIds 318), (.leaf 5 (Common.fact 319).pointIds 319), B0083]
theorem treeEq0082 : B0082.tree = HexagonCover.NBand.M6700_6900.SplitData.node0082 := by
  change Tree.branch (90 : Fin 175) _ = Tree.branch (90 : Fin 175) _
  apply congrArg (Tree.branch (90 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0083

def B0081 : Block := .branch 160 ![1441151880758559105, 302231454904756805305858, 153476910693263469451268, 2923003448886377699927862958680365044377189376008, 11693440346339929630029090606126440435539863765008, 93536104789177786765035829293842113257979683143712, 2854517187409509478984797335390564511401902144] ![(.leaf 0 (Common.fact 320).pointIds 320), B0082, (.leaf 2 (Common.fact 391).pointIds 391), (.leaf 3 (Common.fact 322).pointIds 322), (.leaf 4 (Common.fact 323).pointIds 323), (.leaf 5 (Common.fact 324).pointIds 324), (.leaf 6 (Common.fact 325).pointIds 325)]
theorem treeEq0081 : B0081.tree = HexagonCover.NBand.M6700_6900.SplitData.node0081 := by
  change Tree.branch (160 : Fin 175) _ = Tree.branch (160 : Fin 175) _
  apply congrArg (Tree.branch (160 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0082
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0080 : Block := .branch 161 ![1441151880758559105, 302231454904756805305858, 153476910693263469451268, 174224571863520493293247799005065324290056, 11693440346339929630029090606126440435539863765008, 93536104789177786765035829293842113257979683143712, 2854517187409509478984797335390564511401902144] ![(.leaf 0 (Common.fact 352).pointIds 352), (.leaf 1 (Common.fact 353).pointIds 353), (.leaf 2 (Common.fact 390).pointIds 390), B0081, (.leaf 4 (Common.fact 354).pointIds 354), (.leaf 5 (Common.fact 355).pointIds 355), (.leaf 6 (Common.fact 356).pointIds 356)]
theorem treeEq0080 : B0080.tree = HexagonCover.NBand.M6700_6900.SplitData.node0080 := by
  change Tree.branch (161 : Fin 175) _ = Tree.branch (161 : Fin 175) _
  apply congrArg (Tree.branch (161 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0081
  · rfl
  · rfl
  · rfl

def B0056 : Block := .branch 77 ![1441151880758559105, 302231454904756805305858, 77919046967349146032132, 174224571863678988303902555348386002788360, 11693440346339929630029090606126440435539863765008, 93536104789177786765035829293842113257979683143712, 2854517187409509478984797335390564511401902144] ![(.leaf 0 (Common.fact 300).pointIds 300), B0057, B0080, (.leaf 3 (Common.fact 301).pointIds 301), (.leaf 4 (Common.fact 302).pointIds 302), (.leaf 5 (Common.fact 303).pointIds 303), (.leaf 6 (Common.fact 304).pointIds 304)]
theorem treeEq0056 : B0056.tree = HexagonCover.NBand.M6700_6900.SplitData.node0056 := by
  change Tree.branch (77 : Fin 175) _ = Tree.branch (77 : Fin 175) _
  apply congrArg (Tree.branch (77 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0057
  · exact treeEq0080
  · rfl
  · rfl
  · rfl
  · rfl

def B0088 : Block := .branch 168 ![1441151880758559105, 453347182356585452144130, 2923003274661805836407369740990429765226188511236, 174224571863678988306263738589820825395208, 17539446895663540978325276278564845731007573360656, 93536104789177786765035829293842113257979683143712, 2854517184751053487414965589582950390841212992] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 383).pointIds 383), (.leaf 2 (Common.fact 399).pointIds 399), (.leaf 3 (Common.fact 400).pointIds 400), (.leaf 4 (Common.fact 401).pointIds 401), (.leaf 5 (Common.fact 376).pointIds 376), (.leaf 6 (Common.fact 368).pointIds 368)]
theorem treeEq0088 : B0088.tree = HexagonCover.NBand.M6700_6900.SplitData.node0088 := by
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

def B0087 : Block := .branch 77 ![1441151880758559105, 302231454904756805305858, 2923003274661805836407369740990429765226188511236, 174224571863678988306263738589820825395208, 17539446895663540978325276278564845731007573360656, 93536104789177786765035829293842113257979683143712, 2854517187409509478984797335390564511401902144] ![(.leaf 0 (Common.fact 300).pointIds 300), B0088, (.leaf 2 (Common.fact 398).pointIds 398), (.leaf 3 (Common.fact 301).pointIds 301), (.leaf 4 (Common.fact 302).pointIds 302), (.leaf 5 (Common.fact 303).pointIds 303), (.leaf 6 (Common.fact 304).pointIds 304)]
theorem treeEq0087 : B0087.tree = HexagonCover.NBand.M6700_6900.SplitData.node0087 := by
  change Tree.branch (77 : Fin 175) _ = Tree.branch (77 : Fin 175) _
  apply congrArg (Tree.branch (77 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0088
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0086 : Block := .branch 161 ![1441151880758559105, 302231454904756805305858, 75557863725914323425284, 174224571863678988306263738589820825395208, 17539446895663540978325276278564845731007573360656, 93536104789177786765035829293842113257979683143712, 2854517187409509478984797335390564511401902144] ![(.leaf 0 (Common.fact 352).pointIds 352), (.leaf 1 (Common.fact 353).pointIds 353), B0087, (.leaf 3 (Common.fact 397).pointIds 397), (.leaf 4 (Common.fact 354).pointIds 354), (.leaf 5 (Common.fact 355).pointIds 355), (.leaf 6 (Common.fact 356).pointIds 356)]
theorem treeEq0086 : B0086.tree = HexagonCover.NBand.M6700_6900.SplitData.node0086 := by
  change Tree.branch (161 : Fin 175) _ = Tree.branch (161 : Fin 175) _
  apply congrArg (Tree.branch (161 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0087
  · rfl
  · rfl
  · rfl
  · rfl

def B0085 : Block := .branch 162 ![1441151880758559105, 302231454904756805305858, 75557863725914323425284, 174224571863678988306263738589820825395208, 11693440346339929305510536947699713652383843188752, 93536104789177786765035829293842113257979683143712, 2854517187409509478984797335390564511401902144] ![(.leaf 0 (Common.fact 357).pointIds 357), (.leaf 1 (Common.fact 358).pointIds 358), (.leaf 2 (Common.fact 359).pointIds 359), (.leaf 3 (Common.fact 396).pointIds 396), B0086, (.leaf 5 (Common.fact 360).pointIds 360), (.leaf 6 (Common.fact 361).pointIds 361)]
theorem treeEq0085 : B0085.tree = HexagonCover.NBand.M6700_6900.SplitData.node0085 := by
  change Tree.branch (162 : Fin 175) _ = Tree.branch (162 : Fin 175) _
  apply congrArg (Tree.branch (162 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0086
  · rfl
  · rfl

def B0055 : Block := .branch 71 ![1441151880758559105, 302231454904756805305858, 75557863725914323425284, 174224571863678988303902555348386002788360, 11693440346339929630029090606126440435539863765008, 93536104789177786765035829293842113257979683143712, 2854517187409509478984797335390564511401902144] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), B0056, B0085, (.leaf 4 (Common.fact 298).pointIds 298), (.leaf 5 (Common.fact 299).pointIds 299), (.leaf 0 [] 0)]
theorem treeEq0055 : B0055.tree = HexagonCover.NBand.M6700_6900.SplitData.node0055 := by
  change Tree.branch (71 : Fin 175) _ = Tree.branch (71 : Fin 175) _
  apply congrArg (Tree.branch (71 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0056
  · exact treeEq0085
  · rfl
  · rfl
  · rfl

theorem accepted0055 : B0055.accepted = true := by decide +kernel
theorem checked0055 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6700_6900.SplitData.node0055 (maskNeeds ![1441151880758559105, 302231454904756805305858, 75557863725914323425284, 174224571863678988303902555348386002788360, 11693440346339929630029090606126440435539863765008, 93536104789177786765035829293842113257979683143712, 2854517187409509478984797335390564511401902144]) := by
  rw [← treeEq0055]
  exact B0055.sound accepted0055
#print axioms checked0055

def Tip0048_0055 : Block := .tip HexagonCover.NBand.M6700_6900.SplitData.node0055 ![1441151880758559105, 302231454904756805305858, 75557863725914323425284, 174224571863678988303902555348386002788360, 11693440346339929630029090606126440435539863765008, 93536104789177786765035829293842113257979683143712, 2854517187409509478984797335390564511401902144] checked0055
def B0098 : Block := .branch 168 ![604464350959195345912193, 1461501637330902918203685134947737924412737848834, 77992833943643984238596, 2923003448886377699927862958680365044377189376008, 11693440346339929630029090606126440435539863765008, 93536104789177786765035829293842113257979683143712, 2854517184751053488343420619046985597015556160] ![(.leaf 0 (Common.fact 378).pointIds 378), (.leaf 1 (Common.fact 394).pointIds 394), (.leaf 2 (Common.fact 429).pointIds 429), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 375).pointIds 375), (.leaf 5 (Common.fact 376).pointIds 376), (.leaf 6 (Common.fact 382).pointIds 382)]
theorem treeEq0098 : B0098.tree = HexagonCover.NBand.M6700_6900.SplitData.node0098 := by
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

def B0097 : Block := .branch 79 ![1441151880758559105, 1461501637330902918203685134947737924412737848834, 77992833943643984238596, 2923003448886377699927862958680365044377189376008, 11693440346339929630029090606126440435539863765008, 93536104789177786765035829293842113257979683143712, 2854517187409509480222737374675944786301026368] ![B0098, (.leaf 1 (Common.fact 393).pointIds 393), (.leaf 2 (Common.fact 305).pointIds 305), (.leaf 3 (Common.fact 306).pointIds 306), (.leaf 4 (Common.fact 307).pointIds 307), (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 309).pointIds 309)]
theorem treeEq0097 : B0097.tree = HexagonCover.NBand.M6700_6900.SplitData.node0097 := by
  change Tree.branch (79 : Fin 175) _ = Tree.branch (79 : Fin 175) _
  apply congrArg (Tree.branch (79 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0098
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0096 : Block := .branch 90 ![1441151880758559105, 1461501637330902918203685134947737924412737848834, 77992833943643984238596, 2923003448886377699927862958680365044377189376008, 11693440346339929630029090606126440435539863765008, 93536104789177786765035829293842113257979683143712, 2854517187409509478984797335390564511401902144] ![(.leaf 0 (Common.fact 315).pointIds 315), (.leaf 1 (Common.fact 392).pointIds 392), (.leaf 2 (Common.fact 316).pointIds 316), (.leaf 3 (Common.fact 317).pointIds 317), (.leaf 4 (Common.fact 318).pointIds 318), (.leaf 5 (Common.fact 319).pointIds 319), B0097]
theorem treeEq0096 : B0096.tree = HexagonCover.NBand.M6700_6900.SplitData.node0096 := by
  change Tree.branch (90 : Fin 175) _ = Tree.branch (90 : Fin 175) _
  apply congrArg (Tree.branch (90 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0097

def B0095 : Block := .branch 160 ![1441151880758559105, 302231454904756805305858, 77992833943643984238596, 2923003448886377699927862958680365044377189376008, 11693440346339929630029090606126440435539863765008, 93536104789177786765035829293842113257979683143712, 2854517187409509478984797335390564511401902144] ![(.leaf 0 (Common.fact 320).pointIds 320), B0096, (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 322).pointIds 322), (.leaf 4 (Common.fact 323).pointIds 323), (.leaf 5 (Common.fact 324).pointIds 324), (.leaf 6 (Common.fact 325).pointIds 325)]
theorem treeEq0095 : B0095.tree = HexagonCover.NBand.M6700_6900.SplitData.node0095 := by
  change Tree.branch (160 : Fin 175) _ = Tree.branch (160 : Fin 175) _
  apply congrArg (Tree.branch (160 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0096
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0094 : Block := .branch 71 ![1441151880758559105, 302231454904756805305858, 75631650702209161631748, 2923003448886377699927862958680365044377189376008, 11693440346339929630029090606126440435539863765008, 93536104789177786765035829293842113257979683143712, 2854517187409509478984797335390564511401902144] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), B0095, (.leaf 3 (Common.fact 427).pointIds 427), (.leaf 4 (Common.fact 298).pointIds 298), (.leaf 5 (Common.fact 299).pointIds 299), (.leaf 0 [] 0)]
theorem treeEq0094 : B0094.tree = HexagonCover.NBand.M6700_6900.SplitData.node0094 := by
  change Tree.branch (71 : Fin 175) _ = Tree.branch (71 : Fin 175) _
  apply congrArg (Tree.branch (71 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0095
  · rfl
  · rfl
  · rfl
  · rfl

def B0093 : Block := .branch 72 ![1441151880758559105, 302231454904756805305858, 75631650702209161631748, 2923003448886377699927862958680365044377189376008, 11693440346339929630029090606126440435539863765008, 93536104789177786765035829293842113257979683143712, 2854517187409509478984797335390564511401902144] ![(.leaf 0 (Common.fact 421).pointIds 421), (.leaf 1 (Common.fact 422).pointIds 422), B0094, (.leaf 3 (Common.fact 423).pointIds 423), (.leaf 4 (Common.fact 424).pointIds 424), (.leaf 5 (Common.fact 425).pointIds 425), (.leaf 6 (Common.fact 426).pointIds 426)]
theorem treeEq0093 : B0093.tree = HexagonCover.NBand.M6700_6900.SplitData.node0093 := by
  change Tree.branch (72 : Fin 175) _ = Tree.branch (72 : Fin 175) _
  apply congrArg (Tree.branch (72 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0094
  · rfl
  · rfl
  · rfl
  · rfl

def B0092 : Block := .branch 73 ![1441151880758559105, 302231454904756805305858, 75631650702209161631748, 2923003448886377699927862958680365044377189376008, 11693440346339929630029090606126440435539863765008, 93536104789177786765035829293842113257979683143712, 2854517187409509478984797335390564511401902144] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), B0093, (.leaf 3 (Common.fact 417).pointIds 417), (.leaf 4 (Common.fact 418).pointIds 418), (.leaf 5 (Common.fact 419).pointIds 419), (.leaf 6 (Common.fact 420).pointIds 420)]
theorem treeEq0092 : B0092.tree = HexagonCover.NBand.M6700_6900.SplitData.node0092 := by
  change Tree.branch (73 : Fin 175) _ = Tree.branch (73 : Fin 175) _
  apply congrArg (Tree.branch (73 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0093
  · rfl
  · rfl
  · rfl
  · rfl

def B0091 : Block := .branch 74 ![1441151880758559105, 302231454904756805305858, 75631650702209161631748, 2923003448886377699927862958680365044377189376008, 11693440346339929630029090606126440435539863765008, 93536104789177786765035829293842113257979683143712, 2854517187409509478984797335390564511401902144] ![(.leaf 0 (Common.fact 409).pointIds 409), (.leaf 1 (Common.fact 410).pointIds 410), B0092, (.leaf 3 (Common.fact 411).pointIds 411), (.leaf 4 (Common.fact 412).pointIds 412), (.leaf 5 (Common.fact 413).pointIds 413), (.leaf 6 (Common.fact 414).pointIds 414)]
theorem treeEq0091 : B0091.tree = HexagonCover.NBand.M6700_6900.SplitData.node0091 := by
  change Tree.branch (74 : Fin 175) _ = Tree.branch (74 : Fin 175) _
  apply congrArg (Tree.branch (74 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0092
  · rfl
  · rfl
  · rfl
  · rfl

def B0090 : Block := .branch 75 ![1441151880758559105, 302231454904756805305858, 75631650702209161631748, 2923003448886377699927862958680365044377189376008, 11693440346339929630029090606126440435539863765008, 93536104789177786765035829293842113257979683143712, 2854517187409509478984797335390564511401902144] ![(.leaf 0 (Common.fact 403).pointIds 403), (.leaf 1 (Common.fact 404).pointIds 404), B0091, (.leaf 3 (Common.fact 405).pointIds 405), (.leaf 4 (Common.fact 406).pointIds 406), (.leaf 5 (Common.fact 407).pointIds 407), (.leaf 6 (Common.fact 408).pointIds 408)]
theorem treeEq0090 : B0090.tree = HexagonCover.NBand.M6700_6900.SplitData.node0090 := by
  change Tree.branch (75 : Fin 175) _ = Tree.branch (75 : Fin 175) _
  apply congrArg (Tree.branch (75 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0091
  · rfl
  · rfl
  · rfl
  · rfl

def B0089 : Block := .branch 161 ![1441151880758559105, 302231454904756805305858, 75631650702209161631748, 174224571863520493293247799005065324290056, 11693440346339929630029090606126440435539863765008, 93536104789177786765035829293842113257979683143712, 2854517187409509478984797335390564511401902144] ![(.leaf 0 (Common.fact 352).pointIds 352), (.leaf 1 (Common.fact 353).pointIds 353), (.leaf 2 (Common.fact 402).pointIds 402), B0090, (.leaf 4 (Common.fact 354).pointIds 354), (.leaf 5 (Common.fact 355).pointIds 355), (.leaf 6 (Common.fact 356).pointIds 356)]
theorem treeEq0089 : B0089.tree = HexagonCover.NBand.M6700_6900.SplitData.node0089 := by
  change Tree.branch (161 : Fin 175) _ = Tree.branch (161 : Fin 175) _
  apply congrArg (Tree.branch (161 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0090
  · rfl
  · rfl
  · rfl

def B0054 : Block := .branch 66 ![1441151880758559105, 302231454904756805305858, 75557863725914323425284, 174224571863678988303902555348386002788360, 11693440346339929630029090606126440435539863765008, 93536104789177786765035829293842113257979683143712, 2854517187409509478984797335390564511401902144] ![(.leaf 0 (Common.fact 291).pointIds 291), Tip0048_0055, B0089, (.leaf 3 (Common.fact 292).pointIds 292), (.leaf 4 (Common.fact 293).pointIds 293), (.leaf 5 (Common.fact 294).pointIds 294), (.leaf 6 (Common.fact 295).pointIds 295)]
theorem treeEq0054 : B0054.tree = HexagonCover.NBand.M6700_6900.SplitData.node0054 := by
  change Tree.branch (66 : Fin 175) _ = Tree.branch (66 : Fin 175) _
  apply congrArg (Tree.branch (66 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0089
  · rfl
  · rfl
  · rfl
  · rfl

def B0101 : Block := .branch 168 ![288230376151712129, 453348335278090058991106, 1461501637330902918203684832716283019655932549124, 174224571863678988303902555348386002788360, 11693440346339929630029090606126440435539863765008, 93536104789177786765035829293842113257979683143712, 2854517184751053487414965589582950390841212992] ![(.leaf 0 (Common.fact 432).pointIds 432), (.leaf 1 (Common.fact 433).pointIds 433), (.leaf 2 (Common.fact 434).pointIds 434), (.leaf 3 (Common.fact 385).pointIds 385), (.leaf 4 (Common.fact 375).pointIds 375), (.leaf 5 (Common.fact 376).pointIds 376), (.leaf 6 (Common.fact 368).pointIds 368)]
theorem treeEq0101 : B0101.tree = HexagonCover.NBand.M6700_6900.SplitData.node0101 := by
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

def B0100 : Block := .branch 77 ![288230376151712129, 302232607826261412152834, 1461501637330902918203684832716283019655932549124, 174224571863678988303902555348386002788360, 11693440346339929630029090606126440435539863765008, 93536104789177786765035829293842113257979683143712, 2854517187409509478984797335390564511401902144] ![(.leaf 0 (Common.fact 300).pointIds 300), B0101, (.leaf 2 (Common.fact 431).pointIds 431), (.leaf 3 (Common.fact 301).pointIds 301), (.leaf 4 (Common.fact 302).pointIds 302), (.leaf 5 (Common.fact 303).pointIds 303), (.leaf 6 (Common.fact 304).pointIds 304)]
theorem treeEq0100 : B0100.tree = HexagonCover.NBand.M6700_6900.SplitData.node0100 := by
  change Tree.branch (77 : Fin 175) _ = Tree.branch (77 : Fin 175) _
  apply congrArg (Tree.branch (77 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0101
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0099 : Block := .branch 160 ![288230376151712129, 302232679883855450080770, 6148, 174224571863678988303902555348386002788360, 11693440346339929630029090606126440435539863765008, 93536104789177786765035829293842113257979683143712, 2854517187409509478984797335390564511401902144] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 430).pointIds 430), B0100, (.leaf 3 (Common.fact 322).pointIds 322), (.leaf 4 (Common.fact 323).pointIds 323), (.leaf 5 (Common.fact 324).pointIds 324), (.leaf 6 (Common.fact 325).pointIds 325)]
theorem treeEq0099 : B0099.tree = HexagonCover.NBand.M6700_6900.SplitData.node0099 := by
  change Tree.branch (160 : Fin 175) _ = Tree.branch (160 : Fin 175) _
  apply congrArg (Tree.branch (160 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0100
  · rfl
  · rfl
  · rfl
  · rfl

def B0053 : Block := .branch 60 ![288230376151712129, 302231526962350843233794, 75557863725914323425284, 174224571863678988303902555348386002788360, 11693440346339929630029090606126440435539863765008, 93536104789177786765035829293842113257979683143712, 2854517187409509478984797335390564511401902144] ![B0054, B0099, (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 289).pointIds 289), (.leaf 5 (Common.fact 290).pointIds 290), (.leaf 0 [] 0)]
theorem treeEq0053 : B0053.tree = HexagonCover.NBand.M6700_6900.SplitData.node0053 := by
  change Tree.branch (60 : Fin 175) _ = Tree.branch (60 : Fin 175) _
  apply congrArg (Tree.branch (60 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0054
  · exact treeEq0099
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0052 : Block := .branch 76 ![288230376151712129, 302231526962350843233794, 6148, 174224571863678988303902555348386002788360, 11693440346339929630029090606126440435539863765008, 93536104789177786765035829293842113257979683143712, 2854517187409509478984797335390564511401902144] ![(.leaf 0 (Common.fact 281).pointIds 281), (.leaf 1 (Common.fact 282).pointIds 282), B0053, (.leaf 3 (Common.fact 283).pointIds 283), (.leaf 4 (Common.fact 284).pointIds 284), (.leaf 5 (Common.fact 285).pointIds 285), (.leaf 6 (Common.fact 286).pointIds 286)]
theorem treeEq0052 : B0052.tree = HexagonCover.NBand.M6700_6900.SplitData.node0052 := by
  change Tree.branch (76 : Fin 175) _ = Tree.branch (76 : Fin 175) _
  apply congrArg (Tree.branch (76 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0053
  · rfl
  · rfl
  · rfl
  · rfl

def B0051 : Block := .branch 108 ![288230376151712129, 302231526962350843233794, 6148, 174224571863678988303902555348386002788360, 11693440346339929305510536947699713652383843188752, 93536104789177786765035829293842113257979683143712, 2854517187409509478984797335390564511401902144] ![(.leaf 0 (Common.fact 275).pointIds 275), (.leaf 1 (Common.fact 276).pointIds 276), (.leaf 2 (Common.fact 277).pointIds 277), (.leaf 3 (Common.fact 278).pointIds 278), B0052, (.leaf 5 (Common.fact 279).pointIds 279), (.leaf 6 (Common.fact 280).pointIds 280)]
theorem treeEq0051 : B0051.tree = HexagonCover.NBand.M6700_6900.SplitData.node0051 := by
  change Tree.branch (108 : Fin 175) _ = Tree.branch (108 : Fin 175) _
  apply congrArg (Tree.branch (108 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0052
  · rfl
  · rfl

def B0050 : Block := .branch 119 ![288230376151712129, 302231526962350843233794, 6148, 174224571863758216466416819685979546738696, 11693440346339929305510536947699713652383843188752, 93536104789177786765035829293842113257979683143712, 2854517187409509478984797335390564511401902144] ![(.leaf 0 (Common.fact 158).pointIds 158), (.leaf 1 (Common.fact 159).pointIds 159), (.leaf 2 (Common.fact 160).pointIds 160), (.leaf 3 (Common.fact 161).pointIds 161), B0051, (.leaf 5 (Common.fact 163).pointIds 163), (.leaf 6 (Common.fact 274).pointIds 274)]
theorem treeEq0050 : B0050.tree = HexagonCover.NBand.M6700_6900.SplitData.node0050 := by
  change Tree.branch (119 : Fin 175) _ = Tree.branch (119 : Fin 175) _
  apply congrArg (Tree.branch (119 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0051
  · rfl
  · rfl

def B0049 : Block := .branch 129 ![288230376151712129, 302231526962350843233794, 6148, 174224571863758216466416819685979546738696, 11693440346339929305510536947699713652383843188752, 93536104789177786765035829293842113257979683143712, 2854517187409509478984797335390564511401902144] ![(.leaf 0 (Common.fact 268).pointIds 268), (.leaf 1 (Common.fact 269).pointIds 269), (.leaf 2 (Common.fact 270).pointIds 270), (.leaf 3 (Common.fact 271).pointIds 271), B0050, (.leaf 5 (Common.fact 272).pointIds 272), (.leaf 6 (Common.fact 273).pointIds 273)]
theorem treeEq0049 : B0049.tree = HexagonCover.NBand.M6700_6900.SplitData.node0049 := by
  change Tree.branch (129 : Fin 175) _ = Tree.branch (129 : Fin 175) _
  apply congrArg (Tree.branch (129 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0050
  · rfl
  · rfl

def B0048 : Block := .branch 97 ![288230376151712129, 302231526962350843233794, 6148, 174224571863599760141388291010792458838024, 11693440346339929305510536947699713652383843188752, 93536104789177786765035829293842113257979683143712, 2854517187409509478984797335390564511401902144] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), B0049, (.leaf 4 (Common.fact 265).pointIds 265), (.leaf 5 (Common.fact 266).pointIds 266), (.leaf 6 (Common.fact 267).pointIds 267)]
theorem treeEq0048 : B0048.tree = HexagonCover.NBand.M6700_6900.SplitData.node0048 := by
  change Tree.branch (97 : Fin 175) _ = Tree.branch (97 : Fin 175) _
  apply congrArg (Tree.branch (97 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0049
  · rfl
  · rfl
  · rfl

theorem accepted0048 : B0048.accepted = true := by decide +kernel
theorem checked0048 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6700_6900.SplitData.node0048 (maskNeeds ![288230376151712129, 302231526962350843233794, 6148, 174224571863599760141388291010792458838024, 11693440346339929305510536947699713652383843188752, 93536104789177786765035829293842113257979683143712, 2854517187409509478984797335390564511401902144]) := by
  rw [← treeEq0048]
  exact B0048.sound accepted0048
#print axioms checked0048

def B0152 : Block := .branch 171 ![63802945065326562128765061894766592385, 2192252455996354377305527249074424530583410443778, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 58642753197902479917441407571167582946850313961488, 5575186299632655785383929568162090376888352, 2619010934124200618774995364697211107841430867411008] ![(.leaf 0 (Common.fact 526).pointIds 526), (.leaf 1 (Common.fact 527).pointIds 527), (.leaf 2 (Common.fact 528).pointIds 528), (.leaf 3 (Common.fact 529).pointIds 529), (.leaf 4 (Common.fact 530).pointIds 530), (.leaf 5 (Common.fact 531).pointIds 531), (.leaf 6 (Common.fact 532).pointIds 532)]
theorem treeEq0152 : B0152.tree = HexagonCover.NBand.M6700_6900.SplitData.node0152 := by
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
  · rfl

def B0151 : Block := .branch 170 ![63802945065326562128765061894766592385, 2192252455996354377305527249074424530583410443778, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 58642753197902479917441407571167582946850313961488, 5575186299632655785383929568162090376888352, 1122433257497356030534422095995737295713755943403584] ![(.leaf 0 (Common.fact 520).pointIds 520), (.leaf 1 (Common.fact 521).pointIds 521), (.leaf 2 (Common.fact 522).pointIds 522), (.leaf 3 (Common.fact 523).pointIds 523), (.leaf 4 (Common.fact 524).pointIds 524), (.leaf 5 (Common.fact 525).pointIds 525), B0152]
theorem treeEq0151 : B0151.tree = HexagonCover.NBand.M6700_6900.SplitData.node0151 := by
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
  · exact treeEq0152

def B0150 : Block := .branch 169 ![63802945065326562128765061894766592385, 2192252455996354377305527249074424530583410443778, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 58642753197902479917441407571167582946850313961488, 5575186299632655785383929568162090376888352, 374144419183933736414135461645000389649918481399872] ![(.leaf 0 (Common.fact 514).pointIds 514), (.leaf 1 (Common.fact 515).pointIds 515), (.leaf 2 (Common.fact 516).pointIds 516), (.leaf 3 (Common.fact 517).pointIds 517), (.leaf 4 (Common.fact 518).pointIds 518), (.leaf 5 (Common.fact 519).pointIds 519), B0151]
theorem treeEq0150 : B0150.tree = HexagonCover.NBand.M6700_6900.SplitData.node0150 := by
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
  · exact treeEq0151

def B0155 : Block := .branch 171 ![63802945065326562128765061894766592385, 2192252455996354377305527249074424530583410443778, 2923003274661805836407369743351613006661011118084, 174224571863520570664500254341332505485320, 52796746648578867920108114581875724085070563213328, 5575186299632655785383929568162090376888352, 2619010934124200618774995364697211107841430867411008] ![(.leaf 0 (Common.fact 526).pointIds 526), (.leaf 1 (Common.fact 527).pointIds 527), (.leaf 2 (Common.fact 528).pointIds 528), (.leaf 3 (Common.fact 537).pointIds 537), (.leaf 4 (Common.fact 538).pointIds 538), (.leaf 5 (Common.fact 531).pointIds 531), (.leaf 6 (Common.fact 532).pointIds 532)]
theorem treeEq0155 : B0155.tree = HexagonCover.NBand.M6700_6900.SplitData.node0155 := by
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
  · rfl

def B0154 : Block := .branch 170 ![63802945065326562128765061894766592385, 2192252455996354377305527249074424530583410443778, 2923003274661805836407369743351613006661011118084, 174224571863520570664500254341332505485320, 52796746648578867920108114581875724085070563213328, 5575186299632655785383929568162090376888352, 1122433257497356030534422095995737295713755943403584] ![(.leaf 0 (Common.fact 520).pointIds 520), (.leaf 1 (Common.fact 521).pointIds 521), (.leaf 2 (Common.fact 522).pointIds 522), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 536).pointIds 536), (.leaf 5 (Common.fact 525).pointIds 525), B0155]
theorem treeEq0154 : B0154.tree = HexagonCover.NBand.M6700_6900.SplitData.node0154 := by
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
  · exact treeEq0155

def B0153 : Block := .branch 169 ![63802945065326562128765061894766592385, 2192252455996354377305527249074424530583410443778, 2923003274661805836407369743351613006661011118084, 174224571863520570664500254341332505485320, 52796746648578867920108114581875724085070563213328, 5575186299632655785383929568162090376888352, 374144419183933736414135461645000389649918481399872] ![(.leaf 0 (Common.fact 514).pointIds 514), (.leaf 1 (Common.fact 515).pointIds 515), (.leaf 2 (Common.fact 516).pointIds 516), (.leaf 3 (Common.fact 533).pointIds 533), (.leaf 4 (Common.fact 534).pointIds 534), (.leaf 5 (Common.fact 519).pointIds 519), B0154]
theorem treeEq0153 : B0153.tree = HexagonCover.NBand.M6700_6900.SplitData.node0153 := by
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
  · exact treeEq0154

def B0156 : Block := .branch 169 ![63802945065326562128765061894766592385, 2192252455996354377305527249074424530583410443778, 2923003274661805836407369743351613006661011118084, 174224571863520570664500254341332505485320, 58642753197902479917441407571167582946850313961488, 5575186299632655785383929568162090376888352, 379990425733257348086633443068313375050702398160960] ![(.leaf 0 (Common.fact 514).pointIds 514), (.leaf 1 (Common.fact 515).pointIds 515), (.leaf 2 (Common.fact 516).pointIds 516), (.leaf 3 (Common.fact 533).pointIds 533), (.leaf 4 (Common.fact 518).pointIds 518), (.leaf 5 (Common.fact 519).pointIds 519), (.leaf 6 (Common.fact 539).pointIds 539)]
theorem treeEq0156 : B0156.tree = HexagonCover.NBand.M6700_6900.SplitData.node0156 := by
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

def B0149 : Block := .branch 162 ![63802945065326562128765061894766592385, 2192252455996354377305527249074424530583410443778, 2923003274661805836407369743351613006661011118084, 174224571863520570664500254341332505485320, 58642753197902479917441407571167582946850313961488, 5575186299632655785383929568162090376888352, 374144419183933736414135771130010210994987206180928] ![(.leaf 0 (Common.fact 357).pointIds 357), (.leaf 1 (Common.fact 358).pointIds 358), (.leaf 2 (Common.fact 359).pointIds 359), B0150, B0153, (.leaf 5 (Common.fact 360).pointIds 360), B0156]
theorem treeEq0149 : B0149.tree = HexagonCover.NBand.M6700_6900.SplitData.node0149 := by
  change Tree.branch (162 : Fin 175) _ = Tree.branch (162 : Fin 175) _
  apply congrArg (Tree.branch (162 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0150
  · exact treeEq0153
  · rfl
  · exact treeEq0156

def B0159 : Block := .branch 171 ![63802945065326562128765061894766592385, 2192252455996354377305527249074424530583410443778, 77919046967349146032132, 2923003448886377699927862958680365044377189376008, 58642753197902479917441407571167582946850313961488, 5575186299632655785383929568162090376888352, 2619010934124200618774995364697211107841430867411008] ![(.leaf 0 (Common.fact 526).pointIds 526), (.leaf 1 (Common.fact 527).pointIds 527), (.leaf 2 (Common.fact 544).pointIds 544), (.leaf 3 (Common.fact 545).pointIds 545), (.leaf 4 (Common.fact 530).pointIds 530), (.leaf 5 (Common.fact 531).pointIds 531), (.leaf 6 (Common.fact 532).pointIds 532)]
theorem treeEq0159 : B0159.tree = HexagonCover.NBand.M6700_6900.SplitData.node0159 := by
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
  · rfl

def B0158 : Block := .branch 170 ![63802945065326562128765061894766592385, 2192252455996354377305527249074424530583410443778, 77919046967349146032132, 2923003448886377699927862958680365044377189376008, 58642753197902479917441407571167582946850313961488, 5575186299632655785383929568162090376888352, 1122433257497356030534422095995737295713755943403584] ![(.leaf 0 (Common.fact 520).pointIds 520), (.leaf 1 (Common.fact 521).pointIds 521), (.leaf 2 (Common.fact 542).pointIds 542), (.leaf 3 (Common.fact 543).pointIds 543), (.leaf 4 (Common.fact 524).pointIds 524), (.leaf 5 (Common.fact 525).pointIds 525), B0159]
theorem treeEq0158 : B0158.tree = HexagonCover.NBand.M6700_6900.SplitData.node0158 := by
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
  · exact treeEq0159

def B0157 : Block := .branch 169 ![63802945065326562128765061894766592385, 2192252455996354377305527249074424530583410443778, 77919046967349146032132, 2923003448886377699927862958680365044377189376008, 58642753197902479917441407571167582946850313961488, 5575186299632655785383929568162090376888352, 374144419183933736414135461645000389649918481399872] ![(.leaf 0 (Common.fact 514).pointIds 514), (.leaf 1 (Common.fact 515).pointIds 515), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 518).pointIds 518), (.leaf 5 (Common.fact 519).pointIds 519), B0158]
theorem treeEq0157 : B0157.tree = HexagonCover.NBand.M6700_6900.SplitData.node0157 := by
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
  · exact treeEq0158

def B0160 : Block := .branch 169 ![63802945065326562128765061894766592385, 2192252455996354377305527249074424530583410443778, 77919046967349146032132, 174224571863520570664500254341332505485320, 58642753197902479917441407571167582946850313961488, 5575186299632655785383929568162090376888352, 377067422458595542250542986052937866361764708876352] ![(.leaf 0 (Common.fact 514).pointIds 514), (.leaf 1 (Common.fact 515).pointIds 515), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 533).pointIds 533), (.leaf 4 (Common.fact 518).pointIds 518), (.leaf 5 (Common.fact 519).pointIds 519), (.leaf 6 (Common.fact 546).pointIds 546)]
theorem treeEq0160 : B0160.tree = HexagonCover.NBand.M6700_6900.SplitData.node0160 := by
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

def B0148 : Block := .branch 161 ![63802945065326562128765061894766592385, 2192252455996354377305527249074424530583410443778, 77919046967349146032132, 174224571863520570664500254341332505485320, 58642753197902479917441407571167582946850313961488, 5575186299632655785383929568162090376888352, 374144419183933736414135771130010210994987206180928] ![(.leaf 0 (Common.fact 352).pointIds 352), (.leaf 1 (Common.fact 353).pointIds 353), B0149, B0157, (.leaf 4 (Common.fact 354).pointIds 354), (.leaf 5 (Common.fact 355).pointIds 355), B0160]
theorem treeEq0148 : B0148.tree = HexagonCover.NBand.M6700_6900.SplitData.node0148 := by
  change Tree.branch (161 : Fin 175) _ = Tree.branch (161 : Fin 175) _
  apply congrArg (Tree.branch (161 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0149
  · exact treeEq0157
  · rfl
  · rfl
  · exact treeEq0160

def B0163 : Block := .branch 171 ![63802945065326562128765061894766592385, 730750818665451459101842416358141510927477900802, 1461501637330902918203684835077466261090755155972, 174224571863520570664500254341332505485320, 58642753197902479917441407571167582946850313961488, 5575186299632655785383929568162090376888352, 2619010934124200618774995364697211107841430867411008] ![(.leaf 0 (Common.fact 526).pointIds 526), (.leaf 1 (Common.fact 551).pointIds 551), (.leaf 2 (Common.fact 552).pointIds 552), (.leaf 3 (Common.fact 537).pointIds 537), (.leaf 4 (Common.fact 530).pointIds 530), (.leaf 5 (Common.fact 531).pointIds 531), (.leaf 6 (Common.fact 532).pointIds 532)]
theorem treeEq0163 : B0163.tree = HexagonCover.NBand.M6700_6900.SplitData.node0163 := by
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
  · rfl

def B0162 : Block := .branch 170 ![63802945065326562128765061894766592385, 730750818665451459101842416358141510927477900802, 1461501637330902918203684835077466261090755155972, 174224571863520570664500254341332505485320, 58642753197902479917441407571167582946850313961488, 5575186299632655785383929568162090376888352, 1122433257497356030534422095995737295713755943403584] ![(.leaf 0 (Common.fact 520).pointIds 520), (.leaf 1 (Common.fact 549).pointIds 549), (.leaf 2 (Common.fact 550).pointIds 550), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 524).pointIds 524), (.leaf 5 (Common.fact 525).pointIds 525), B0163]
theorem treeEq0162 : B0162.tree = HexagonCover.NBand.M6700_6900.SplitData.node0162 := by
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
  · exact treeEq0163

def B0161 : Block := .branch 169 ![63802945065326562128765061894766592385, 730750818665451459101842416358141510927477900802, 1461501637330902918203684835077466261090755155972, 174224571863520570664500254341332505485320, 58642753197902479917441407571167582946850313961488, 5575186299632655785383929568162090376888352, 374144419183933736414135461645000389649918481399872] ![(.leaf 0 (Common.fact 514).pointIds 514), (.leaf 1 (Common.fact 547).pointIds 547), (.leaf 2 (Common.fact 548).pointIds 548), (.leaf 3 (Common.fact 533).pointIds 533), (.leaf 4 (Common.fact 518).pointIds 518), (.leaf 5 (Common.fact 519).pointIds 519), B0162]
theorem treeEq0161 : B0161.tree = HexagonCover.NBand.M6700_6900.SplitData.node0161 := by
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
  · exact treeEq0162

def B0164 : Block := .branch 171 ![63802945065326562128765061894766592385, 730750818665451459101842416358141510927477900802, 77919046967349146032132, 174224571863520570664500254341332505485320, 58642753197902479917441407571167582946850313961488, 5575186299632655785383929568162090376888352, 375605920821264639332339146477716672669574413942848] ![(.leaf 0 (Common.fact 526).pointIds 526), (.leaf 1 (Common.fact 551).pointIds 551), (.leaf 2 (Common.fact 544).pointIds 544), (.leaf 3 (Common.fact 537).pointIds 537), (.leaf 4 (Common.fact 530).pointIds 530), (.leaf 5 (Common.fact 531).pointIds 531), (.leaf 6 (Common.fact 553).pointIds 553)]
theorem treeEq0164 : B0164.tree = HexagonCover.NBand.M6700_6900.SplitData.node0164 := by
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
  · rfl

def B0147 : Block := .branch 160 ![63802945065326562128765061894766592385, 730750818665451459101842416358141510927477900802, 77919046967349146032132, 174224571863520570664500254341332505485320, 58642753197902479917441407571167582946850313961488, 5575186299632655785383929568162090376888352, 374144419183933736414135771130010210994987206180928] ![(.leaf 0 (Common.fact 320).pointIds 320), B0148, B0161, (.leaf 3 (Common.fact 322).pointIds 322), (.leaf 4 (Common.fact 323).pointIds 323), (.leaf 5 (Common.fact 324).pointIds 324), B0164]
theorem treeEq0147 : B0147.tree = HexagonCover.NBand.M6700_6900.SplitData.node0147 := by
  change Tree.branch (160 : Fin 175) _ = Tree.branch (160 : Fin 175) _
  apply congrArg (Tree.branch (160 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0148
  · exact treeEq0161
  · rfl
  · rfl
  · rfl
  · exact treeEq0164

theorem accepted0147 : B0147.accepted = true := by decide +kernel
theorem checked0147 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6700_6900.SplitData.node0147 (maskNeeds ![63802945065326562128765061894766592385, 730750818665451459101842416358141510927477900802, 77919046967349146032132, 174224571863520570664500254341332505485320, 58642753197902479917441407571167582946850313961488, 5575186299632655785383929568162090376888352, 374144419183933736414135771130010210994987206180928]) := by
  rw [← treeEq0147]
  exact B0147.sound accepted0147
#print axioms checked0147

end HexagonCover.NBand.M6700_6900.SplitTree.Run0000
