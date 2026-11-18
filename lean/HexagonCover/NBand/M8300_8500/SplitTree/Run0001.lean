import HexagonCover.NBand.M8300_8500.SplitData
import HexagonCover.NBand.M8300_8500.SplitTree.Run0000
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.SplitTree.Run0001
open OwnerTree HexagonCover.NBand.M8300_8500

abbrev Block := Chunk (n := 177) (Certificate := Fin 1786) (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck

def Tip0056_0059 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node0059 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 89551430602463689901512333669182293900550152, 365375409332726378588028525032524321226024386576, 5709034369502101269473775122669557740833472544, 11172171938396184191083481572113328159326272] HexagonCover.NBand.M8300_8500.SplitTree.Run0000.checked0059
def B0135 : Block := .branch 171 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 89551430602463689901512333669182293900550152, 2854495385412568799223888792352556584806744080, 365375452931403991296161839423942332109285621792, 2619010934096978029421003220227579171223980872302656] ![(.leaf 0 (Common.fact 476).pointIds 476), (.leaf 1 (Common.fact 477).pointIds 477), (.leaf 2 (Common.fact 432).pointIds 432), (.leaf 3 (Common.fact 463).pointIds 463), (.leaf 4 (Common.fact 486).pointIds 486), (.leaf 5 (Common.fact 487).pointIds 487), (.leaf 6 (Common.fact 383).pointIds 383)]
theorem treeEq0135 : B0135.tree = HexagonCover.NBand.M8300_8500.SplitData.node0135 := by
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

def B0134 : Block := .branch 170 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 89551430602463689901512333669182293900550152, 2854495385412568799223888792352556584806744080, 365375452931403991296161839423942332109285621792, 1122433257470133441180429951526105359096305948295232] ![(.leaf 0 (Common.fact 474).pointIds 474), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 430).pointIds 430), (.leaf 3 (Common.fact 460).pointIds 460), (.leaf 4 (Common.fact 484).pointIds 484), (.leaf 5 (Common.fact 485).pointIds 485), B0135]
theorem treeEq0134 : B0134.tree = HexagonCover.NBand.M8300_8500.SplitData.node0134 := by
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
  · exact treeEq0135

def B0133 : Block := .branch 98 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 89551430602463689901512333669182293900550152, 11694867594032635914428702550522616713832267087888, 365375452931403991296161839423942332109285621792, 1122433257470133441180429951526105359096305948295232] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), B0134, (.leaf 4 (Common.fact 483).pointIds 483), (.leaf 5 (Common.fact 334).pointIds 334), (.leaf 6 (Common.fact 473).pointIds 473)]
theorem treeEq0133 : B0133.tree = HexagonCover.NBand.M8300_8500.SplitData.node0133 := by
  change Tree.branch (98 : Fin 177) _ = Tree.branch (98 : Fin 177) _
  apply congrArg (Tree.branch (98 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0134
  · rfl
  · rfl
  · rfl

def B0132 : Block := .branch 108 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 89551430602463689901512333669182293900550152, 11694867594032635914428702550522616713832267087888, 365375452931403991296161839423942332109285621792, 1122433268620506040445741522293964495420486701285440] ![(.leaf 0 (Common.fact 452).pointIds 452), (.leaf 1 (Common.fact 453).pointIds 453), (.leaf 2 (Common.fact 454).pointIds 454), B0133, (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 456).pointIds 456), (.leaf 6 (Common.fact 472).pointIds 472)]
theorem treeEq0132 : B0132.tree = HexagonCover.NBand.M8300_8500.SplitData.node0132 := by
  change Tree.branch (108 : Fin 177) _ = Tree.branch (108 : Fin 177) _
  apply congrArg (Tree.branch (108 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0133
  · rfl
  · rfl
  · rfl

def B0131 : Block := .branch 163 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 89551430602463689901512333669182293900550152, 2854495385412568799223888792352556584806744080, 365375452931403991296161839423942332109285621792, 1122433268620506040445741522293964495420486701285440] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B0132, (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 471).pointIds 471)]
theorem treeEq0131 : B0131.tree = HexagonCover.NBand.M8300_8500.SplitData.node0131 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0132
  · rfl
  · rfl

def B0130 : Block := .branch 169 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 89551430602463689901512333669182293900550152, 2854495385412568799223888792352556584806744080, 365375452931403991296161839423942332109285621792, 374144430307083746325454887943227589356649239281728] ![(.leaf 0 (Common.fact 466).pointIds 466), (.leaf 1 (Common.fact 470).pointIds 470), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 444).pointIds 444), (.leaf 4 (Common.fact 480).pointIds 480), (.leaf 5 (Common.fact 481).pointIds 481), B0131]
theorem treeEq0130 : B0130.tree = HexagonCover.NBand.M8300_8500.SplitData.node0130 := by
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
  · exact treeEq0131

def B0129 : Block := .branch 168 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 89551430602463689901512333669182293900550152, 2854495385412568799223888792352556584806744080, 365375452931403991296161839423942332109285621792, 11150372599265311570767859136324730508279872] ![(.leaf 0 (Common.fact 468).pointIds 468), (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 424).pointIds 424), (.leaf 3 (Common.fact 443).pointIds 443), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), B0130]
theorem treeEq0129 : B0129.tree = HexagonCover.NBand.M8300_8500.SplitData.node0129 := by
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
  · exact treeEq0130

def B0058 : Block := .branch 158 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 89551430602463689901512333669182293900550152, 2854495385412568799223888792352556584806744080, 5709034369502101269473775122669557740833472544, 11172171938396184191083481572113328159326272] ![(.leaf 0 (Common.fact 306).pointIds 306), (.leaf 1 (Common.fact 307).pointIds 307), (.leaf 2 (Common.fact 308).pointIds 308), (.leaf 3 (Common.fact 309).pointIds 309), Tip0056_0059, B0129, (.leaf 0 [] 0)]
theorem treeEq0058 : B0058.tree = HexagonCover.NBand.M8300_8500.SplitData.node0058 := by
  change Tree.branch (158 : Fin 177) _ = Tree.branch (158 : Fin 177) _
  apply congrArg (Tree.branch (158 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0129
  · rfl

def B0141 : Block := .branch 170 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 89551430602463689901512333669182293900550152, 2854495385412568799223888792352556584806744080, 22344343876792368382166963144225556808466464, 1122438966460904265019954184669983157076851479281728] ![(.leaf 0 (Common.fact 474).pointIds 474), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 430).pointIds 430), (.leaf 3 (Common.fact 460).pointIds 460), (.leaf 4 (Common.fact 484).pointIds 484), (.leaf 5 (Common.fact 493).pointIds 493), (.leaf 6 (Common.fact 494).pointIds 494)]
theorem treeEq0141 : B0141.tree = HexagonCover.NBand.M8300_8500.SplitData.node0141 := by
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
  · rfl

def B0140 : Block := .branch 169 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 89551430602463689901512333669182293900550152, 2854495385412568799223888792352556584806744080, 22344343876792368382166963144225556808466464, 374150128147481970899667550319246251013014017278016] ![(.leaf 0 (Common.fact 466).pointIds 466), (.leaf 1 (Common.fact 470).pointIds 470), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 444).pointIds 444), (.leaf 4 (Common.fact 480).pointIds 480), (.leaf 5 (Common.fact 492).pointIds 492), B0141]
theorem treeEq0140 : B0140.tree = HexagonCover.NBand.M8300_8500.SplitData.node0140 := by
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
  · exact treeEq0141

def B0139 : Block := .branch 98 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 89551430602463689901512333669182293900550152, 11694867594032635914428702550522616713832267087888, 22344343876792368382166963144225556808466464, 374150128147481970899667550319246251013014017278016] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), B0140, (.leaf 4 (Common.fact 483).pointIds 483), (.leaf 5 (Common.fact 334).pointIds 334), (.leaf 6 (Common.fact 491).pointIds 491)]
theorem treeEq0139 : B0139.tree = HexagonCover.NBand.M8300_8500.SplitData.node0139 := by
  change Tree.branch (98 : Fin 177) _ = Tree.branch (98 : Fin 177) _
  apply congrArg (Tree.branch (98 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0140
  · rfl
  · rfl
  · rfl

def B0138 : Block := .branch 108 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 89551430602463689901512333669182293900550152, 11694867594032635914428702550522616713832267087888, 22344343876792368382166963144225556808466464, 374150128147503238547600108973212711925978502791232] ![(.leaf 0 (Common.fact 452).pointIds 452), (.leaf 1 (Common.fact 453).pointIds 453), (.leaf 2 (Common.fact 454).pointIds 454), B0139, (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 456).pointIds 456), (.leaf 6 (Common.fact 490).pointIds 490)]
theorem treeEq0138 : B0138.tree = HexagonCover.NBand.M8300_8500.SplitData.node0138 := by
  change Tree.branch (108 : Fin 177) _ = Tree.branch (108 : Fin 177) _
  apply congrArg (Tree.branch (108 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0139
  · rfl
  · rfl
  · rfl

def B0137 : Block := .branch 163 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 89551430602463689901512333669182293900550152, 2854495385412568799223888792352556584806744080, 22344343876792368382166963144225556808466464, 374150128147503238547600108973212711925978502791232] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B0138, (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 489).pointIds 489)]
theorem treeEq0137 : B0137.tree = HexagonCover.NBand.M8300_8500.SplitData.node0137 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0138
  · rfl
  · rfl

def B0136 : Block := .branch 168 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 89551430602463689901512333669182293900550152, 2854495385412568799223888792352556584806744080, 22344343876792368382166963144225556808466464, 5708990792091487456791797844258894059771789376] ![(.leaf 0 (Common.fact 468).pointIds 468), (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 424).pointIds 424), (.leaf 3 (Common.fact 443).pointIds 443), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 488).pointIds 488), B0137]
theorem treeEq0136 : B0136.tree = HexagonCover.NBand.M8300_8500.SplitData.node0136 := by
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
  · exact treeEq0137

def B0057 : Block := .branch 152 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 89551430602463689901512333669182293900550152, 2854495385412568799223888792352556584806744080, 22344343876792368382166963144225556808466464, 11172171938396184191083481572113328159326272] ![(.leaf 0 (Common.fact 301).pointIds 301), (.leaf 1 (Common.fact 302).pointIds 302), (.leaf 2 (Common.fact 303).pointIds 303), (.leaf 3 (Common.fact 304).pointIds 304), (.leaf 4 (Common.fact 305).pointIds 305), B0058, B0136]
theorem treeEq0057 : B0057.tree = HexagonCover.NBand.M8300_8500.SplitData.node0057 := by
  change Tree.branch (152 : Fin 177) _ = Tree.branch (152 : Fin 177) _
  apply congrArg (Tree.branch (152 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0058
  · exact treeEq0136

def B0145 : Block := .branch 171 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 89551430602463689901512333669182293900550152, 5575186300281692892700783021728402417745936, 5709034369502101269473775122669557740833472544, 1122436111965518853100192068098044258086578713788480] ![(.leaf 0 (Common.fact 476).pointIds 476), (.leaf 1 (Common.fact 477).pointIds 477), (.leaf 2 (Common.fact 432).pointIds 432), (.leaf 3 (Common.fact 463).pointIds 463), (.leaf 4 (Common.fact 498).pointIds 498), (.leaf 5 (Common.fact 382).pointIds 382), (.leaf 6 (Common.fact 499).pointIds 499)]
theorem treeEq0145 : B0145.tree = HexagonCover.NBand.M8300_8500.SplitData.node0145 := by
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

def B0144 : Block := .branch 169 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 89551430602463689901512333669182293900550152, 5575186300281692892700783021728402417745936, 5709034369502101269473775122669557740833472544, 374147273652096558979905433747307352022741251784768] ![(.leaf 0 (Common.fact 466).pointIds 466), (.leaf 1 (Common.fact 470).pointIds 470), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 444).pointIds 444), (.leaf 4 (Common.fact 497).pointIds 497), (.leaf 5 (Common.fact 370).pointIds 370), B0145]
theorem treeEq0144 : B0144.tree = HexagonCover.NBand.M8300_8500.SplitData.node0144 := by
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
  · exact treeEq0145

def B0143 : Block := .branch 168 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 89551430602463689901512333669182293900550152, 5575186300281692892700783021728402417745936, 5709034369502101269473775122669557740833472544, 2854495385411919762116571938898990822520782912] ![(.leaf 0 (Common.fact 468).pointIds 468), (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 424).pointIds 424), (.leaf 3 (Common.fact 443).pointIds 443), (.leaf 4 (Common.fact 496).pointIds 496), (.leaf 5 (Common.fact 364).pointIds 364), B0144]
theorem treeEq0143 : B0143.tree = HexagonCover.NBand.M8300_8500.SplitData.node0143 := by
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
  · exact treeEq0144

def B0142 : Block := .branch 152 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 89551430602463689901512333669182293900550152, 5575186300281692892700783021728402417745936, 43598678261745240631244871577195302486048, 2854517184751050634736887561334779420171829312] ![(.leaf 0 (Common.fact 301).pointIds 301), (.leaf 1 (Common.fact 302).pointIds 302), (.leaf 2 (Common.fact 303).pointIds 303), (.leaf 3 (Common.fact 304).pointIds 304), (.leaf 4 (Common.fact 305).pointIds 305), B0143, (.leaf 6 (Common.fact 495).pointIds 495)]
theorem treeEq0142 : B0142.tree = HexagonCover.NBand.M8300_8500.SplitData.node0142 := by
  change Tree.branch (152 : Fin 177) _ = Tree.branch (152 : Fin 177) _
  apply congrArg (Tree.branch (152 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0143
  · rfl

def B0056 : Block := .branch 151 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 89551430602463689901512333669182293900550152, 5575186300281692892700783021728402417745936, 22344343876792368382166963144225556808466464, 11172171938396184191083481572113328159326272] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), (.leaf 2 (Common.fact 298).pointIds 298), (.leaf 3 (Common.fact 299).pointIds 299), B0057, (.leaf 5 (Common.fact 300).pointIds 300), B0142]
theorem treeEq0056 : B0056.tree = HexagonCover.NBand.M8300_8500.SplitData.node0056 := by
  change Tree.branch (151 : Fin 177) _ = Tree.branch (151 : Fin 177) _
  apply congrArg (Tree.branch (151 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0057
  · rfl
  · exact treeEq0142

theorem accepted0056 : B0056.accepted = true := by decide +kernel
theorem checked0056 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node0056 (maskNeeds ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 89551430602463689901512333669182293900550152, 5575186300281692892700783021728402417745936, 22344343876792368382166963144225556808466464, 11172171938396184191083481572113328159326272]) := by
  rw [← treeEq0056]
  exact B0056.sound accepted0056
#print axioms checked0056

def Tip0053_0056 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node0056 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 89551430602463689901512333669182293900550152, 5575186300281692892700783021728402417745936, 22344343876792368382166963144225556808466464, 11172171938396184191083481572113328159326272] checked0056
def B0150 : Block := .branch 169 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 348449808341197335369460578588847876628488, 94778167094404185458843656112321848441667600, 233840284317288343704957955401568427370506015342624, 385836443405730969671084366604957853513896699625536] ![(.leaf 0 (Common.fact 466).pointIds 466), (.leaf 1 (Common.fact 470).pointIds 470), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 511).pointIds 511), (.leaf 4 (Common.fact 512).pointIds 512), (.leaf 5 (Common.fact 513).pointIds 513), (.leaf 6 (Common.fact 448).pointIds 448)]
theorem treeEq0150 : B0150.tree = HexagonCover.NBand.M8300_8500.SplitData.node0150 := by
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

def B0149 : Block := .branch 168 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 348449808341197335369460578588847876628488, 94778167094404185458843656112321848441667600, 233840284317288343704957955401568427370506015342624, 11692024249019822610941049429589400481977968623680] ![(.leaf 0 (Common.fact 468).pointIds 468), (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 424).pointIds 424), (.leaf 3 (Common.fact 508).pointIds 508), (.leaf 4 (Common.fact 509).pointIds 509), (.leaf 5 (Common.fact 510).pointIds 510), B0150]
theorem treeEq0149 : B0149.tree = HexagonCover.NBand.M8300_8500.SplitData.node0149 := by
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
  · exact treeEq0150

def B0148 : Block := .branch 163 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 348449808341197335369460578588847876628488, 94778167094404185458843656112321848441667600, 233840284317288343704957955401568427370506015342624, 11150372599265311570767859136324730508279872] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 507).pointIds 507), (.leaf 5 (Common.fact 329).pointIds 329), B0149]
theorem treeEq0148 : B0148.tree = HexagonCover.NBand.M8300_8500.SplitData.node0148 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0149

def B0147 : Block := .branch 165 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 348449808341197335369460578588847876628488, 94778167094404185458843656112321848441667600, 187072231922699450322440040754647370741516173967392, 11150372599265311570767859136324730508279872] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 506).pointIds 506), B0148, (.leaf 0 [] 0)]
theorem treeEq0147 : B0147.tree = HexagonCover.NBand.M8300_8500.SplitData.node0147 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0148
  · rfl

def B0146 : Block := .branch 167 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 348449808341197335369460578588847876628488, 94778167094404185458843656112321848441667600, 22344343876792368382166963144225556808466464, 11150372599265311570767859136324730508279872] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 504).pointIds 504), B0147, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq0146 : B0146.tree = HexagonCover.NBand.M8300_8500.SplitData.node0146 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0147
  · rfl

def B0055 : Block := .branch 146 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 348449808341197335369460578588847876628488, 5575186300281692892700783021728402417745936, 22344343876792368382166963144225556808466464, 11172171938396184191083481572113328159326272] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), Tip0053_0056, B0146, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq0055 : B0055.tree = HexagonCover.NBand.M8300_8500.SplitData.node0055 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0146
  · rfl
  · rfl

def B0158 : Block := .branch 170 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 348449808341197335369460578588847876628488, 2854495385412568799223888792352556584806744080, 43598678261745240631244871577195302486048, 1122433279770878639711053093061823631744667454275648] ![(.leaf 0 (Common.fact 474).pointIds 474), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 430).pointIds 430), (.leaf 3 (Common.fact 521).pointIds 521), (.leaf 4 (Common.fact 484).pointIds 484), (.leaf 5 (Common.fact 522).pointIds 522), (.leaf 6 (Common.fact 523).pointIds 523)]
theorem treeEq0158 : B0158.tree = HexagonCover.NBand.M8300_8500.SplitData.node0158 := by
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
  · rfl

def B0157 : Block := .branch 169 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 348449808341197335369460578588847876628488, 2854495385412568799223888792352556584806744080, 43598678261745240631244871577195302486048, 374144441457456345590766458711086725680829992271936] ![(.leaf 0 (Common.fact 466).pointIds 466), (.leaf 1 (Common.fact 470).pointIds 470), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 511).pointIds 511), (.leaf 4 (Common.fact 480).pointIds 480), (.leaf 5 (Common.fact 520).pointIds 520), B0158]
theorem treeEq0157 : B0157.tree = HexagonCover.NBand.M8300_8500.SplitData.node0157 := by
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
  · exact treeEq0158

def B0156 : Block := .branch 98 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 348449808341197335369460578588847876628488, 11694867594032635914428702550522616713832267087888, 43598678261745240631244871577195302486048, 374144452607828944856078029478945862005010745262144] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), B0157, (.leaf 4 (Common.fact 483).pointIds 483), (.leaf 5 (Common.fact 334).pointIds 334), (.leaf 6 (Common.fact 519).pointIds 519)]
theorem treeEq0156 : B0156.tree = HexagonCover.NBand.M8300_8500.SplitData.node0156 := by
  change Tree.branch (98 : Fin 177) _ = Tree.branch (98 : Fin 177) _
  apply congrArg (Tree.branch (98 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0157
  · rfl
  · rfl
  · rfl

def B0155 : Block := .branch 108 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 348449808341197335369460578588847876628488, 11694867594032635914428702550522616713832267087888, 43598678261745240631244871577195302486048, 374144452607850212504010588132912322917975230775360] ![(.leaf 0 (Common.fact 452).pointIds 452), (.leaf 1 (Common.fact 453).pointIds 453), (.leaf 2 (Common.fact 454).pointIds 454), B0156, (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 456).pointIds 456), (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq0155 : B0155.tree = HexagonCover.NBand.M8300_8500.SplitData.node0155 := by
  change Tree.branch (108 : Fin 177) _ = Tree.branch (108 : Fin 177) _
  apply congrArg (Tree.branch (108 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0156
  · rfl
  · rfl
  · rfl

def B0154 : Block := .branch 146 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 348449808341197335369460578588847876628488, 11694867594032635914428702550522616713832267087888, 43598678261745240631244871577195302486048, 374144452607850212504010588132912322917975230775360] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), B0155, (.leaf 4 (Common.fact 517).pointIds 517), (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq0154 : B0154.tree = HexagonCover.NBand.M8300_8500.SplitData.node0154 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0155
  · rfl
  · rfl
  · rfl

def B0153 : Block := .branch 163 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 348449808341197335369460578588847876628488, 2854495385412568799223888792352556584806744080, 43598678261745240631244871577195302486048, 374144452607850212504010588132912322917975230775360] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B0154, (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 516).pointIds 516)]
theorem treeEq0153 : B0153.tree = HexagonCover.NBand.M8300_8500.SplitData.node0153 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0154
  · rfl
  · rfl

def B0152 : Block := .branch 168 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 348449808341197335369460578588847876628488, 2854495385412568799223888792352556584806744080, 43598678261745240631244871577195302486048, 33451139065443867270957543869886056499773504] ![(.leaf 0 (Common.fact 468).pointIds 468), (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 424).pointIds 424), (.leaf 3 (Common.fact 508).pointIds 508), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 515).pointIds 515), B0153]
theorem treeEq0152 : B0152.tree = HexagonCover.NBand.M8300_8500.SplitData.node0152 := by
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
  · exact treeEq0153

def B0151 : Block := .branch 151 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 348449808341197335369460578588847876628488, 649037107316853453566312041250832, 43598678261745240631244871577195302486048, 33451139065443867270957543869886056499773504] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), (.leaf 2 (Common.fact 298).pointIds 298), (.leaf 3 (Common.fact 299).pointIds 299), B0152, (.leaf 5 (Common.fact 300).pointIds 300), (.leaf 6 (Common.fact 514).pointIds 514)]
theorem treeEq0151 : B0151.tree = HexagonCover.NBand.M8300_8500.SplitData.node0151 := by
  change Tree.branch (151 : Fin 177) _ = Tree.branch (151 : Fin 177) _
  apply congrArg (Tree.branch (151 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0152
  · rfl
  · rfl

def B0054 : Block := .branch 144 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 348449808341197335369460578588847876628488, 5575186300281692892700783021728402417745936, 43598678261745240631244871577195302486048, 11172171938396184191083481572113328159326272] ![(.leaf 0 (Common.fact 287).pointIds 287), (.leaf 1 (Common.fact 288).pointIds 288), (.leaf 2 (Common.fact 289).pointIds 289), (.leaf 3 (Common.fact 290).pointIds 290), (.leaf 4 (Common.fact 291).pointIds 291), B0055, B0151]
theorem treeEq0054 : B0054.tree = HexagonCover.NBand.M8300_8500.SplitData.node0054 := by
  change Tree.branch (144 : Fin 177) _ = Tree.branch (144 : Fin 177) _
  apply congrArg (Tree.branch (144 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0055
  · exact treeEq0151

def B0162 : Block := .branch 171 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 348449808341197335369460578588847876628488, 5444518519772122732267447285220332634128, 5709034369502101269473775122669557740833472544, 1122433263045319740813085736910034927258396324790336] ![(.leaf 0 (Common.fact 476).pointIds 476), (.leaf 1 (Common.fact 477).pointIds 477), (.leaf 2 (Common.fact 432).pointIds 432), (.leaf 3 (Common.fact 527).pointIds 527), (.leaf 4 (Common.fact 528).pointIds 528), (.leaf 5 (Common.fact 382).pointIds 382), (.leaf 6 (Common.fact 529).pointIds 529)]
theorem treeEq0162 : B0162.tree = HexagonCover.NBand.M8300_8500.SplitData.node0162 := by
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

def B0161 : Block := .branch 169 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 348449808341197335369460578588847876628488, 5444518519772122732267447285220332634128, 5709034369502101269473775122669557740833472544, 374144424731897446692799102559298021194558862786624] ![(.leaf 0 (Common.fact 466).pointIds 466), (.leaf 1 (Common.fact 470).pointIds 470), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 511).pointIds 511), (.leaf 4 (Common.fact 526).pointIds 526), (.leaf 5 (Common.fact 370).pointIds 370), B0162]
theorem treeEq0161 : B0161.tree = HexagonCover.NBand.M8300_8500.SplitData.node0161 := by
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
  · exact treeEq0162

def B0160 : Block := .branch 168 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 348449808341197335369460578588847876628488, 5444518519772122732267447285220332634128, 5709034369502101269473775122669557740833472544, 5575186299632655785383929568162640131784768] ![(.leaf 0 (Common.fact 468).pointIds 468), (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 424).pointIds 424), (.leaf 3 (Common.fact 508).pointIds 508), (.leaf 4 (Common.fact 525).pointIds 525), (.leaf 5 (Common.fact 364).pointIds 364), B0161]
theorem treeEq0160 : B0160.tree = HexagonCover.NBand.M8300_8500.SplitData.node0160 := by
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
  · exact treeEq0161

def B0159 : Block := .branch 152 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 348449808341197335369460578588847876628488, 5444518519772122732267447285220332634128, 43598678261745240631244871577195302486048, 16747358238028839976467411140275418535821376] ![(.leaf 0 (Common.fact 301).pointIds 301), (.leaf 1 (Common.fact 302).pointIds 302), (.leaf 2 (Common.fact 303).pointIds 303), (.leaf 3 (Common.fact 304).pointIds 304), (.leaf 4 (Common.fact 305).pointIds 305), B0160, (.leaf 6 (Common.fact 524).pointIds 524)]
theorem treeEq0159 : B0159.tree = HexagonCover.NBand.M8300_8500.SplitData.node0159 := by
  change Tree.branch (152 : Fin 177) _ = Tree.branch (152 : Fin 177) _
  apply congrArg (Tree.branch (152 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0160
  · rfl

def B0053 : Block := .branch 142 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 348449808341197335369460578588847876628488, 5444518519772122732267447285220332634128, 43598678261745240631244871577195302486048, 11172171938396184191083481572113328159326272] ![(.leaf 0 (Common.fact 282).pointIds 282), (.leaf 1 (Common.fact 283).pointIds 283), (.leaf 2 (Common.fact 284).pointIds 284), (.leaf 3 (Common.fact 285).pointIds 285), B0054, (.leaf 5 (Common.fact 286).pointIds 286), B0159]
theorem treeEq0053 : B0053.tree = HexagonCover.NBand.M8300_8500.SplitData.node0053 := by
  change Tree.branch (142 : Fin 177) _ = Tree.branch (142 : Fin 177) _
  apply congrArg (Tree.branch (142 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0054
  · rfl
  · exact treeEq0159

theorem accepted0053 : B0053.accepted = true := by decide +kernel
theorem checked0053 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node0053 (maskNeeds ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 348449808341197335369460578588847876628488, 5444518519772122732267447285220332634128, 43598678261745240631244871577195302486048, 11172171938396184191083481572113328159326272]) := by
  rw [← treeEq0053]
  exact B0053.sound accepted0053
#print axioms checked0053

def Tip0050_0053 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node0053 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 348449808341197335369460578588847876628488, 5444518519772122732267447285220332634128, 43598678261745240631244871577195302486048, 11172171938396184191083481572113328159326272] checked0053
def B0167 : Block := .branch 169 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 681229347998225709891729793580764520456, 353893662246813109318763045295350981165072, 233840262016543145174334813865850154722144509362208, 385836443405730969671084366604957853513896699625536] ![(.leaf 0 (Common.fact 466).pointIds 466), (.leaf 1 (Common.fact 470).pointIds 470), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 536).pointIds 536), (.leaf 4 (Common.fact 537).pointIds 537), (.leaf 5 (Common.fact 538).pointIds 538), (.leaf 6 (Common.fact 448).pointIds 448)]
theorem treeEq0167 : B0167.tree = HexagonCover.NBand.M8300_8500.SplitData.node0167 := by
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

def B0166 : Block := .branch 168 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 681229347998225709891729793580764520456, 353893662246813109318763045295350981165072, 233840262016543145174334813865850154722144509362208, 11692024249019822610941049429589400481977968623680] ![(.leaf 0 (Common.fact 468).pointIds 468), (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 424).pointIds 424), (.leaf 3 (Common.fact 533).pointIds 533), (.leaf 4 (Common.fact 534).pointIds 534), (.leaf 5 (Common.fact 535).pointIds 535), B0167]
theorem treeEq0166 : B0166.tree = HexagonCover.NBand.M8300_8500.SplitData.node0166 := by
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
  · exact treeEq0167

def B0165 : Block := .branch 163 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 681229347998225709891729793580764520456, 353893662246813109318763045295350981165072, 233840262016543145174334813865850154722144509362208, 11150372599265311570767859136324730508279872] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 532).pointIds 532), (.leaf 5 (Common.fact 329).pointIds 329), B0166]
theorem treeEq0165 : B0165.tree = HexagonCover.NBand.M8300_8500.SplitData.node0165 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0166

def B0164 : Block := .branch 165 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 681229347998225709891729793580764520456, 353893662246813109318763045295350981165072, 187072209621954251791816899218929098093154667986976, 11150372599265311570767859136324730508279872] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 531).pointIds 531), B0165, (.leaf 0 [] 0)]
theorem treeEq0164 : B0164.tree = HexagonCover.NBand.M8300_8500.SplitData.node0164 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0165
  · rfl

def B0163 : Block := .branch 167 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 681229347998225709891729793580764520456, 353893662246813109318763045295350981165072, 43598678261745240631244871577195302486048, 11150372599265311570767859136324730508279872] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 530).pointIds 530), B0164, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq0163 : B0163.tree = HexagonCover.NBand.M8300_8500.SplitData.node0163 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0164
  · rfl

def B0052 : Block := .branch 138 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 681229347998225709891729793580764520456, 5444518519772122732267447285220332634128, 43598678261745240631244871577195302486048, 11172177255308167330746973187341569280704576] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), Tip0050_0053, B0163, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq0052 : B0052.tree = HexagonCover.NBand.M8300_8500.SplitData.node0052 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0163
  · rfl
  · rfl

def B0170 : Block := .branch 171 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 681229347998225709891729793580764520456, 5444518519772122732267447285220332634128, 42535295865117307932921825928971419680, 1122433257513689584146310074849417308847572279361600] ![(.leaf 0 (Common.fact 476).pointIds 476), (.leaf 1 (Common.fact 477).pointIds 477), (.leaf 2 (Common.fact 432).pointIds 432), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 528).pointIds 528), (.leaf 5 (Common.fact 542).pointIds 542), (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq0170 : B0170.tree = HexagonCover.NBand.M8300_8500.SplitData.node0170 := by
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

def B0169 : Block := .branch 169 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 681229347998225709891729793580764520456, 5444518519772122732267447285220332634128, 42535295865117307932921825928971419680, 374144419200267290026023440498680402783734817357888] ![(.leaf 0 (Common.fact 466).pointIds 466), (.leaf 1 (Common.fact 470).pointIds 470), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 536).pointIds 536), (.leaf 4 (Common.fact 526).pointIds 526), (.leaf 5 (Common.fact 540).pointIds 540), B0170]
theorem treeEq0169 : B0169.tree = HexagonCover.NBand.M8300_8500.SplitData.node0169 := by
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
  · exact treeEq0170

def B0168 : Block := .branch 168 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 681229347998225709891729793580764520456, 5444518519772122732267447285220332634128, 42535295865117307932921825928971419680, 43556142965880123323311949751816086356032] ![(.leaf 0 (Common.fact 468).pointIds 468), (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 424).pointIds 424), (.leaf 3 (Common.fact 533).pointIds 533), (.leaf 4 (Common.fact 525).pointIds 525), (.leaf 5 (Common.fact 539).pointIds 539), B0169]
theorem treeEq0168 : B0168.tree = HexagonCover.NBand.M8300_8500.SplitData.node0168 := by
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
  · exact treeEq0169

def B0051 : Block := .branch 135 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 681229347998225709891729793580764520456, 5444518519772122732267447285220332634128, 42535295865117307932921825928971419680, 11172177255308167330746973187341569280704576] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), B0052, B0168]
theorem treeEq0051 : B0051.tree = HexagonCover.NBand.M8300_8500.SplitData.node0051 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0052
  · exact treeEq0168

def B0174 : Block := .branch 171 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 681229347998225709891729793580764520456, 2659105028677148599261180432601939984, 5708990813359135389350451810719806474502406176, 1122433257475577959051164966941519352815214239678528] ![(.leaf 0 (Common.fact 476).pointIds 476), (.leaf 1 (Common.fact 477).pointIds 477), (.leaf 2 (Common.fact 432).pointIds 432), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 549).pointIds 549), (.leaf 5 (Common.fact 550).pointIds 550), (.leaf 6 (Common.fact 551).pointIds 551)]
theorem treeEq0174 : B0174.tree = HexagonCover.NBand.M8300_8500.SplitData.node0174 := by
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

def B0173 : Block := .branch 169 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 681229347998225709891729793580764520456, 2659105028677148599261180432601939984, 5708990813359135389350451810719806474502406176, 374144419162155664930878332590782446751376777674816] ![(.leaf 0 (Common.fact 466).pointIds 466), (.leaf 1 (Common.fact 470).pointIds 470), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 536).pointIds 536), (.leaf 4 (Common.fact 547).pointIds 547), (.leaf 5 (Common.fact 548).pointIds 548), B0174]
theorem treeEq0173 : B0173.tree = HexagonCover.NBand.M8300_8500.SplitData.node0173 := by
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
  · exact treeEq0174

def B0172 : Block := .branch 168 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 681229347998225709891729793580764520456, 2659105028677148599261180432601939984, 5708990813359135389350451810719806474502406176, 5444517870735015415413993719458046672960] ![(.leaf 0 (Common.fact 468).pointIds 468), (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 424).pointIds 424), (.leaf 3 (Common.fact 533).pointIds 533), (.leaf 4 (Common.fact 545).pointIds 545), (.leaf 5 (Common.fact 546).pointIds 546), B0173]
theorem treeEq0172 : B0172.tree = HexagonCover.NBand.M8300_8500.SplitData.node0172 := by
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
  · exact treeEq0173

def B0171 : Block := .branch 152 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 681229347998225709891729793580764520456, 2659105028677148599261180432601939984, 42535295865117307932921825928971419680, 11177616456266919206498895565832236450709568] ![(.leaf 0 (Common.fact 301).pointIds 301), (.leaf 1 (Common.fact 302).pointIds 302), (.leaf 2 (Common.fact 303).pointIds 303), (.leaf 3 (Common.fact 304).pointIds 304), (.leaf 4 (Common.fact 305).pointIds 305), B0172, (.leaf 6 (Common.fact 544).pointIds 544)]
theorem treeEq0171 : B0171.tree = HexagonCover.NBand.M8300_8500.SplitData.node0171 := by
  change Tree.branch (152 : Fin 177) _ = Tree.branch (152 : Fin 177) _
  apply congrArg (Tree.branch (152 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0172
  · rfl

def B0050 : Block := .branch 132 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 681229347998225709891729793580764520456, 2659105028677148599261180432601939984, 42535295865117307932921825928971419680, 11172177255308167330746973187341569280704576] ![(.leaf 0 (Common.fact 267).pointIds 267), (.leaf 1 (Common.fact 268).pointIds 268), (.leaf 2 (Common.fact 269).pointIds 269), (.leaf 3 (Common.fact 270).pointIds 270), B0051, (.leaf 5 (Common.fact 271).pointIds 271), B0171]
theorem treeEq0050 : B0050.tree = HexagonCover.NBand.M8300_8500.SplitData.node0050 := by
  change Tree.branch (132 : Fin 177) _ = Tree.branch (132 : Fin 177) _
  apply congrArg (Tree.branch (132 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0051
  · rfl
  · exact treeEq0171

theorem accepted0050 : B0050.accepted = true := by decide +kernel
theorem checked0050 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node0050 (maskNeeds ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 681229347998225709891729793580764520456, 2659105028677148599261180432601939984, 42535295865117307932921825928971419680, 11172177255308167330746973187341569280704576]) := by
  rw [← treeEq0050]
  exact B0050.sound accepted0050
#print axioms checked0050

def B0193 : Block := .branch 163 ![385, 1538, 6148, 24584, 2944046815350418332776618161041160161479196688, 393248, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 584).pointIds 584), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq0193 : B0193.tree = HexagonCover.NBand.M8300_8500.SplitData.node0193 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0192 : Block := .branch 151 ![385, 1538, 6148, 24584, 89551429938498570660046222142169888713703440, 393248, 3367299783604371601068346665977420085189194389389376] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), (.leaf 2 (Common.fact 298).pointIds 298), (.leaf 3 (Common.fact 299).pointIds 299), B0193, (.leaf 5 (Common.fact 300).pointIds 300), (.leaf 6 (Common.fact 583).pointIds 583)]
theorem treeEq0192 : B0192.tree = HexagonCover.NBand.M8300_8500.SplitData.node0192 := by
  change Tree.branch (151 : Fin 177) _ = Tree.branch (151 : Fin 177) _
  apply congrArg (Tree.branch (151 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0193
  · rfl
  · rfl

def B0191 : Block := .branch 88 ![385, 1538, 2923003274661805836407374501135844497828563916804, 24584, 89551429938498570660046222142169888713703440, 393248, 3367299783604371601068346665977420085189194389389376] ![(.leaf 0 (Common.fact 577).pointIds 577), B0192, (.leaf 2 (Common.fact 578).pointIds 578), (.leaf 3 (Common.fact 579).pointIds 579), (.leaf 4 (Common.fact 580).pointIds 580), (.leaf 5 (Common.fact 581).pointIds 581), (.leaf 6 (Common.fact 582).pointIds 582)]
theorem treeEq0191 : B0191.tree = HexagonCover.NBand.M8300_8500.SplitData.node0191 := by
  change Tree.branch (88 : Fin 177) _ = Tree.branch (88 : Fin 177) _
  apply congrArg (Tree.branch (88 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0192
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0190 : Block := .branch 161 ![385, 1538, 4835703278458516698830852, 1496577676626845252854571161159410264031205064204296, 89551429938498570660046222142169888713703440, 393248, 3367299783604371601068346665977420085189194389389376] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), B0191, (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 576).pointIds 576)]
theorem treeEq0190 : B0190.tree = HexagonCover.NBand.M8300_8500.SplitData.node0190 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0191
  · rfl
  · rfl
  · rfl
  · rfl

def B0189 : Block := .branch 135 ![385, 1538, 4835703278458516698830852, 1496577676626845252854571161159410264031205064204296, 89551429938498570660046222142169888713703440, 982129100286366761032876207585342189208786669273120, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 574).pointIds 574), B0190]
theorem treeEq0189 : B0189.tree = HexagonCover.NBand.M8300_8500.SplitData.node0189 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0190

def B0188 : Block := .branch 169 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 1496577676626845252854729617484438792706392152104968, 89551432596954562229877967949784009274392592, 233840261972944466912589573234605283144949207269408, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 466).pointIds 466), (.leaf 1 (Common.fact 470).pointIds 470), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 558).pointIds 558), (.leaf 4 (Common.fact 547).pointIds 547), B0189, (.leaf 6 (Common.fact 573).pointIds 573)]
theorem treeEq0188 : B0188.tree = HexagonCover.NBand.M8300_8500.SplitData.node0188 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0189
  · rfl

def B0187 : Block := .branch 86 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 1496577676626845252854729617484438792706392152104968, 89551432596954562229877967949784009274392592, 233840261972944466912589573234605283144949207269408, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), B0188, (.leaf 3 (Common.fact 571).pointIds 571), (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 572).pointIds 572)]
theorem treeEq0187 : B0187.tree = HexagonCover.NBand.M8300_8500.SplitData.node0187 := by
  change Tree.branch (86 : Fin 177) _ = Tree.branch (86 : Fin 177) _
  apply congrArg (Tree.branch (86 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0188
  · rfl
  · rfl
  · rfl
  · rfl

def B0186 : Block := .branch 138 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 1496577676626845252854729617484438792706392152104968, 89202983453227521243291472351773878625861648, 233840261972944466912589573234605283144949207269408, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 570).pointIds 570), B0187, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq0186 : B0186.tree = HexagonCover.NBand.M8300_8500.SplitData.node0186 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0187
  · rfl
  · rfl

def B0185 : Block := .branch 165 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 1496577676626845252854729617484438792706392152104968, 89202983453227521243291472351773878625861648, 187072209578355573530071658587684226515959365894176, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 569).pointIds 569), B0186, (.leaf 0 [] 0)]
theorem treeEq0185 : B0185.tree = HexagonCover.NBand.M8300_8500.SplitData.node0185 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0186
  · rfl

def B0184 : Block := .branch 167 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 1496577676626845252854729617484438792706392152104968, 89202983453227521243291472351773878625861648, 393248, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 568).pointIds 568), B0185, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq0184 : B0184.tree = HexagonCover.NBand.M8300_8500.SplitData.node0184 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0185
  · rfl

def B0183 : Block := .branch 146 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 1496577676626845252854729617484438792706392152104968, 2659105028677148599261180432601939984, 393248, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 567).pointIds 567), B0184, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq0183 : B0183.tree = HexagonCover.NBand.M8300_8500.SplitData.node0183 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0184
  · rfl
  · rfl

def B0182 : Block := .branch 170 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 664614156348782964980578717228097544, 2659105028677148599261180432601939984, 393248, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 474).pointIds 474), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 430).pointIds 430), B0183, (.leaf 4 (Common.fact 564).pointIds 564), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq0182 : B0182.tree = HexagonCover.NBand.M8300_8500.SplitData.node0182 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0183
  · rfl
  · rfl
  · rfl

def B0181 : Block := .branch 171 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 664614156348782964980578717228097544, 2659105028677148599261180432601939984, 393248, 374144430328930937664175765230274562199416982732864] ![(.leaf 0 (Common.fact 476).pointIds 476), (.leaf 1 (Common.fact 477).pointIds 477), (.leaf 2 (Common.fact 432).pointIds 432), (.leaf 3 (Common.fact 562).pointIds 562), (.leaf 4 (Common.fact 549).pointIds 549), (.leaf 5 (Common.fact 563).pointIds 563), B0182]
theorem treeEq0181 : B0181.tree = HexagonCover.NBand.M8300_8500.SplitData.node0181 := by
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
  · exact treeEq0182

def B0180 : Block := .branch 168 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 664614156348782964980578717228097544, 2659105028677148599261180432601939984, 393248, 11172219790604032448054906109167498251731008] ![(.leaf 0 (Common.fact 468).pointIds 468), (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 424).pointIds 424), (.leaf 3 (Common.fact 555).pointIds 555), (.leaf 4 (Common.fact 545).pointIds 545), (.leaf 5 (Common.fact 561).pointIds 561), B0181]
theorem treeEq0180 : B0180.tree = HexagonCover.NBand.M8300_8500.SplitData.node0180 := by
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
  · exact treeEq0181

theorem accepted0180 : B0180.accepted = true := by decide +kernel
theorem checked0180 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node0180 (maskNeeds ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 664614156348782964980578717228097544, 2659105028677148599261180432601939984, 393248, 11172219790604032448054906109167498251731008]) := by
  rw [← treeEq0180]
  exact B0180.sound accepted0180
#print axioms checked0180

end HexagonCover.NBand.M8300_8500.SplitTree.Run0001
