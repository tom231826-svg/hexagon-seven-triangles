import HexagonCover.NBand.M8500_8700.SplitData
import HexagonCover.NBand.M8500_8700.SplitTree.Run0005
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8500_8700.SplitTree.Run0006
open OwnerTree HexagonCover.NBand.M8500_8700

abbrev Block := Chunk (n := 175) (Certificate := Fin 1173) (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck

def Tip0046_0349 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node0349 ![1238242271318996484309909889, 226673591178292726072834, 362677764331132826121410564, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448] HexagonCover.NBand.M8500_8700.SplitTree.Run0005.checked0349
def Tip0046_0048 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node0048 ![1238242271318996484309909889, 309636125548797447127434754, 130601785896986981739534340, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448] HexagonCover.NBand.M8500_8700.SplitTree.Run0005.checked0048
def B0476 : Block := .branch 171 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 5986310706507378352962293074805895248510699696054280, 1329227995784915872903807060280442896, 393248, 1461512831302180445260496231820290921581742915648] ![(.leaf 0 (Common.fact 743).pointIds 743), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 772).pointIds 772), (.leaf 3 (Common.fact 780).pointIds 780), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 781).pointIds 781)]
theorem treeEq0476 : B0476.tree = HexagonCover.NBand.M8500_8700.SplitData.node0476 := by
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

def B0475 : Block := .branch 172 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 24584, 1329227995784915872903807060280442896, 393248, 1461512831302180445260496231820290921581742915648] ![(.leaf 0 (Common.fact 740).pointIds 740), (.leaf 1 (Common.fact 769).pointIds 769), (.leaf 2 (Common.fact 770).pointIds 770), B0476, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 779).pointIds 779)]
theorem treeEq0475 : B0475.tree = HexagonCover.NBand.M8500_8700.SplitData.node0475 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0476
  · rfl
  · rfl
  · rfl

def B0474 : Block := .branch 160 ![1238242271318996484309909889, 619196693233868430175634946, 362677745884388752411858948, 24584, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 777).pointIds 777), (.leaf 2 (Common.fact 778).pointIds 778), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), B0475]
theorem treeEq0474 : B0474.tree = HexagonCover.NBand.M8500_8700.SplitData.node0474 := by
  change Tree.branch (160 : Fin 175) _ = Tree.branch (160 : Fin 175) _
  apply congrArg (Tree.branch (160 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0475

def B0348 : Block := .branch 89 ![1238242271318996484309909889, 226673591178292726072834, 362677764331132826121410564, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448] ![Tip0046_0349, B0474, (.leaf 2 (Common.fact 270).pointIds 270), (.leaf 3 (Common.fact 271).pointIds 271), (.leaf 4 (Common.fact 272).pointIds 272), (.leaf 5 (Common.fact 273).pointIds 273), (.leaf 6 (Common.fact 274).pointIds 274)]
theorem treeEq0348 : B0348.tree = HexagonCover.NBand.M8500_8700.SplitData.node0348 := by
  change Tree.branch (89 : Fin 175) _ = Tree.branch (89 : Fin 175) _
  apply congrArg (Tree.branch (89 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0474
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0047 : Block := .branch 88 ![1238242271318996484309909889, 226673591178292726072834, 130601785896986981739534340, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 265).pointIds 265), Tip0046_0048, B0348, (.leaf 3 (Common.fact 266).pointIds 266), (.leaf 4 (Common.fact 267).pointIds 267), (.leaf 5 (Common.fact 268).pointIds 268), (.leaf 6 (Common.fact 269).pointIds 269)]
theorem treeEq0047 : B0047.tree = HexagonCover.NBand.M8500_8700.SplitData.node0047 := by
  change Tree.branch (88 : Fin 175) _ = Tree.branch (88 : Fin 175) _
  apply congrArg (Tree.branch (88 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0348
  · rfl
  · rfl
  · rfl
  · rfl

def B0486 : Block := .branch 169 ![1238242271318996484309909889, 226673591178292726072834, 53230514994906640848787460, 89551429937849850542750678201290218029473800, 5846006549323611672814739330865132078623730270224, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 775).pointIds 775), (.leaf 2 (Common.fact 794).pointIds 794), (.leaf 3 (Common.fact 795).pointIds 795), (.leaf 4 (Common.fact 796).pointIds 796), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq0486 : B0486.tree = HexagonCover.NBand.M8500_8700.SplitData.node0486 := by
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

def B0485 : Block := .branch 170 ![1238242271318996484309909889, 226673591178292726072834, 53230514994906640848787460, 89551429937849850542750678201290218029473800, 5846006549323611672814739330865132078623730270224, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 773).pointIds 773), (.leaf 2 (Common.fact 790).pointIds 790), (.leaf 3 (Common.fact 791).pointIds 791), (.leaf 4 (Common.fact 792).pointIds 792), B0486, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq0485 : B0485.tree = HexagonCover.NBand.M8500_8700.SplitData.node0485 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0486
  · rfl

def B0484 : Block := .branch 171 ![1238242271318996484309909889, 226673591178292726072834, 53230514994906640848787460, 89551429937849850542750678201290218029473800, 5846006549323611672814739330865132078623730270224, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 743).pointIds 743), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 787).pointIds 787), (.leaf 3 (Common.fact 788).pointIds 788), (.leaf 4 (Common.fact 789).pointIds 789), (.leaf 5 (Common.fact 566).pointIds 566), B0485]
theorem treeEq0484 : B0484.tree = HexagonCover.NBand.M8500_8700.SplitData.node0484 := by
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
  · exact treeEq0485

def B0483 : Block := .branch 98 ![1238242271318996484309909889, 226673591178292726072834, 53230533441650714558339076, 89551429937849533630100621143939843853672456, 5846006549323611672814739330865132078623730270224, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 275).pointIds 275), (.leaf 1 (Common.fact 276).pointIds 276), (.leaf 2 (Common.fact 277).pointIds 277), B0484, (.leaf 4 (Common.fact 732).pointIds 732), (.leaf 5 (Common.fact 278).pointIds 278), (.leaf 6 (Common.fact 279).pointIds 279)]
theorem treeEq0483 : B0483.tree = HexagonCover.NBand.M8500_8700.SplitData.node0483 := by
  change Tree.branch (98 : Fin 175) _ = Tree.branch (98 : Fin 175) _
  apply congrArg (Tree.branch (98 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0484
  · rfl
  · rfl
  · rfl

def B0482 : Block := .branch 108 ![1238242271318996484309909889, 226673591178292726072834, 53230533441650714558339076, 89551429937849533630100621143939843853672456, 5846006549323611672814739330865132078623730270224, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), B0483, (.leaf 4 (Common.fact 712).pointIds 712), (.leaf 5 (Common.fact 288).pointIds 288), (.leaf 6 (Common.fact 289).pointIds 289)]
theorem treeEq0482 : B0482.tree = HexagonCover.NBand.M8500_8700.SplitData.node0482 := by
  change Tree.branch (108 : Fin 175) _ = Tree.branch (108 : Fin 175) _
  apply congrArg (Tree.branch (108 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0483
  · rfl
  · rfl
  · rfl

def B0481 : Block := .branch 119 ![1238242271318996484309909889, 226673591178292726072834, 53230533441650714558339076, 89551429937849533630100621143939843853672456, 5846006549323611672814739330865132078623730270224, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 310).pointIds 310), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), B0482, (.leaf 4 (Common.fact 786).pointIds 786), (.leaf 5 (Common.fact 313).pointIds 313), (.leaf 6 (Common.fact 314).pointIds 314)]
theorem treeEq0481 : B0481.tree = HexagonCover.NBand.M8500_8700.SplitData.node0481 := by
  change Tree.branch (119 : Fin 175) _ = Tree.branch (119 : Fin 175) _
  apply congrArg (Tree.branch (119 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0482
  · rfl
  · rfl
  · rfl

def B0480 : Block := .branch 129 ![1238242271318996484309909889, 226673591178292726072834, 53230533441650714558339076, 89551429937849533630100621143939843853672456, 5846006549323611672814739330865132078623730270224, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), (.leaf 2 (Common.fact 322).pointIds 322), B0481, (.leaf 4 (Common.fact 785).pointIds 785), (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 6 (Common.fact 324).pointIds 324)]
theorem treeEq0480 : B0480.tree = HexagonCover.NBand.M8500_8700.SplitData.node0480 := by
  change Tree.branch (129 : Fin 175) _ = Tree.branch (129 : Fin 175) _
  apply congrArg (Tree.branch (129 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0481
  · rfl
  · rfl
  · rfl

def B0479 : Block := .branch 138 ![1238242271318996484309909889, 226673591178292726072834, 53230533441650714558339076, 89202980794122492643514125545929713205141512, 5846006549323611672814739330865132078623730270224, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), B0480, (.leaf 4 (Common.fact 784).pointIds 784), (.leaf 5 (Common.fact 333).pointIds 333), (.leaf 6 (Common.fact 334).pointIds 334)]
theorem treeEq0479 : B0479.tree = HexagonCover.NBand.M8500_8700.SplitData.node0479 := by
  change Tree.branch (138 : Fin 175) _ = Tree.branch (138 : Fin 175) _
  apply congrArg (Tree.branch (138 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0480
  · rfl
  · rfl
  · rfl

def B0478 : Block := .branch 146 ![1238242271318996484309909889, 226673591178292726072834, 53230533441650714558339076, 77371252455336267181219848, 5846006549323611672814739330865132078623730270224, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 347).pointIds 347), B0479, (.leaf 4 (Common.fact 783).pointIds 783), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 0 [] 0)]
theorem treeEq0478 : B0478.tree = HexagonCover.NBand.M8500_8700.SplitData.node0478 := by
  change Tree.branch (146 : Fin 175) _ = Tree.branch (146 : Fin 175) _
  apply congrArg (Tree.branch (146 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0479
  · rfl
  · rfl
  · rfl

def B0477 : Block := .branch 162 ![1238242271318996484309909889, 226673591178292726072834, 53230533441650714558339076, 77371252455336267181219848, 98320, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 373).pointIds 373), (.leaf 1 (Common.fact 374).pointIds 374), (.leaf 2 (Common.fact 375).pointIds 375), (.leaf 3 (Common.fact 782).pointIds 782), B0478, (.leaf 5 (Common.fact 376).pointIds 376), (.leaf 6 (Common.fact 377).pointIds 377)]
theorem treeEq0477 : B0477.tree = HexagonCover.NBand.M8500_8700.SplitData.node0477 := by
  change Tree.branch (162 : Fin 175) _ = Tree.branch (162 : Fin 175) _
  apply congrArg (Tree.branch (162 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0478
  · rfl
  · rfl

def B0046 : Block := .branch 86 ![1238242271318996484309909889, 226673591178292726072834, 53230533441650714558339076, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 260).pointIds 260), (.leaf 1 (Common.fact 261).pointIds 261), B0047, B0477, (.leaf 4 (Common.fact 262).pointIds 262), (.leaf 5 (Common.fact 263).pointIds 263), (.leaf 6 (Common.fact 264).pointIds 264)]
theorem treeEq0046 : B0046.tree = HexagonCover.NBand.M8500_8700.SplitData.node0046 := by
  change Tree.branch (86 : Fin 175) _ = Tree.branch (86 : Fin 175) _
  apply congrArg (Tree.branch (86 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0047
  · exact treeEq0477
  · rfl
  · rfl
  · rfl

theorem accepted0046 : B0046.accepted = true := by decide +kernel
theorem checked0046 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node0046 (maskNeeds ![1238242271318996484309909889, 226673591178292726072834, 53230533441650714558339076, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq0046]
  exact B0046.sound accepted0046
#print axioms checked0046

def Tip0045_0046 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node0046 ![1238242271318996484309909889, 226673591178292726072834, 53230533441650714558339076, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448] checked0046
def B0496 : Block := .branch 169 ![1238242271318996484309909889, 226673591178292726072834, 33887701881072574053488644, 89551429937849850504065051973622084438876168, 5846006549323611672814739330865132078623730270224, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 775).pointIds 775), (.leaf 2 (Common.fact 803).pointIds 803), (.leaf 3 (Common.fact 804).pointIds 804), (.leaf 4 (Common.fact 796).pointIds 796), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq0496 : B0496.tree = HexagonCover.NBand.M8500_8700.SplitData.node0496 := by
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

def B0495 : Block := .branch 170 ![1238242271318996484309909889, 226673591178292726072834, 33887701881072574053488644, 89551429937849850504065051973622084438876168, 5846006549323611672814739330865132078623730270224, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 773).pointIds 773), (.leaf 2 (Common.fact 801).pointIds 801), (.leaf 3 (Common.fact 802).pointIds 802), (.leaf 4 (Common.fact 792).pointIds 792), B0496, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq0495 : B0495.tree = HexagonCover.NBand.M8500_8700.SplitData.node0495 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0496
  · rfl

def B0494 : Block := .branch 171 ![1238242271318996484309909889, 226673591178292726072834, 33887701881072574053488644, 89551429937849850504065051973622084438876168, 5846006549323611672814739330865132078623730270224, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 743).pointIds 743), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 799).pointIds 799), (.leaf 3 (Common.fact 800).pointIds 800), (.leaf 4 (Common.fact 789).pointIds 789), (.leaf 5 (Common.fact 566).pointIds 566), B0495]
theorem treeEq0494 : B0494.tree = HexagonCover.NBand.M8500_8700.SplitData.node0494 := by
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
  · exact treeEq0495

def B0493 : Block := .branch 98 ![1238242271318996484309909889, 226673591178292726072834, 33887720327816647763040260, 89551429937849533591414994916271710263074824, 5846006549323611672814739330865132078623730270224, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 275).pointIds 275), (.leaf 1 (Common.fact 276).pointIds 276), (.leaf 2 (Common.fact 277).pointIds 277), B0494, (.leaf 4 (Common.fact 732).pointIds 732), (.leaf 5 (Common.fact 278).pointIds 278), (.leaf 6 (Common.fact 279).pointIds 279)]
theorem treeEq0493 : B0493.tree = HexagonCover.NBand.M8500_8700.SplitData.node0493 := by
  change Tree.branch (98 : Fin 175) _ = Tree.branch (98 : Fin 175) _
  apply congrArg (Tree.branch (98 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0494
  · rfl
  · rfl
  · rfl

def B0492 : Block := .branch 108 ![1238242271318996484309909889, 226673591178292726072834, 33887720327816647763040260, 89551429937849533591414994916271710263074824, 5846006549323611672814739330865132078623730270224, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), B0493, (.leaf 4 (Common.fact 712).pointIds 712), (.leaf 5 (Common.fact 288).pointIds 288), (.leaf 6 (Common.fact 289).pointIds 289)]
theorem treeEq0492 : B0492.tree = HexagonCover.NBand.M8500_8700.SplitData.node0492 := by
  change Tree.branch (108 : Fin 175) _ = Tree.branch (108 : Fin 175) _
  apply congrArg (Tree.branch (108 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0493
  · rfl
  · rfl
  · rfl

def B0491 : Block := .branch 119 ![1238242271318996484309909889, 226673591178292726072834, 33887720327816647763040260, 89551429937849533591414994916271710263074824, 5846006549323611672814739330865132078623730270224, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 310).pointIds 310), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), B0492, (.leaf 4 (Common.fact 786).pointIds 786), (.leaf 5 (Common.fact 313).pointIds 313), (.leaf 6 (Common.fact 314).pointIds 314)]
theorem treeEq0491 : B0491.tree = HexagonCover.NBand.M8500_8700.SplitData.node0491 := by
  change Tree.branch (119 : Fin 175) _ = Tree.branch (119 : Fin 175) _
  apply congrArg (Tree.branch (119 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0492
  · rfl
  · rfl
  · rfl

def B0490 : Block := .branch 129 ![1238242271318996484309909889, 226673591178292726072834, 33887720327816647763040260, 89551429937849533591414994916271710263074824, 5846006549323611672814739330865132078623730270224, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), (.leaf 2 (Common.fact 322).pointIds 322), B0491, (.leaf 4 (Common.fact 785).pointIds 785), (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 6 (Common.fact 324).pointIds 324)]
theorem treeEq0490 : B0490.tree = HexagonCover.NBand.M8500_8700.SplitData.node0490 := by
  change Tree.branch (129 : Fin 175) _ = Tree.branch (129 : Fin 175) _
  apply congrArg (Tree.branch (129 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0491
  · rfl
  · rfl
  · rfl

def B0489 : Block := .branch 138 ![1238242271318996484309909889, 226673591178292726072834, 33887720327816647763040260, 89202980794122492604828499318261579614543880, 5846006549323611672814739330865132078623730270224, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), B0490, (.leaf 4 (Common.fact 784).pointIds 784), (.leaf 5 (Common.fact 333).pointIds 333), (.leaf 6 (Common.fact 334).pointIds 334)]
theorem treeEq0489 : B0489.tree = HexagonCover.NBand.M8500_8700.SplitData.node0489 := by
  change Tree.branch (138 : Fin 175) _ = Tree.branch (138 : Fin 175) _
  apply congrArg (Tree.branch (138 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0490
  · rfl
  · rfl
  · rfl

def B0488 : Block := .branch 146 ![1238242271318996484309909889, 226673591178292726072834, 33887720327816647763040260, 38685626227668133590622216, 5846006549323611672814739330865132078623730270224, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 347).pointIds 347), B0489, (.leaf 4 (Common.fact 783).pointIds 783), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 0 [] 0)]
theorem treeEq0488 : B0488.tree = HexagonCover.NBand.M8500_8700.SplitData.node0488 := by
  change Tree.branch (146 : Fin 175) _ = Tree.branch (146 : Fin 175) _
  apply congrArg (Tree.branch (146 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0489
  · rfl
  · rfl
  · rfl

def B0487 : Block := .branch 162 ![1238242271318996484309909889, 226673591178292726072834, 33887720327816647763040260, 158495010654756343320678522888, 98320, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 373).pointIds 373), (.leaf 1 (Common.fact 374).pointIds 374), (.leaf 2 (Common.fact 375).pointIds 375), (.leaf 3 (Common.fact 798).pointIds 798), B0488, (.leaf 5 (Common.fact 376).pointIds 376), (.leaf 6 (Common.fact 377).pointIds 377)]
theorem treeEq0487 : B0487.tree = HexagonCover.NBand.M8500_8700.SplitData.node0487 := by
  change Tree.branch (162 : Fin 175) _ = Tree.branch (162 : Fin 175) _
  apply congrArg (Tree.branch (162 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0488
  · rfl
  · rfl

def B0045 : Block := .branch 85 ![1238242271318996484309909889, 226673591178292726072834, 33887720327816647763040260, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 255).pointIds 255), (.leaf 1 (Common.fact 256).pointIds 256), Tip0045_0046, B0487, (.leaf 4 (Common.fact 257).pointIds 257), (.leaf 5 (Common.fact 258).pointIds 258), (.leaf 6 (Common.fact 259).pointIds 259)]
theorem treeEq0045 : B0045.tree = HexagonCover.NBand.M8500_8700.SplitData.node0045 := by
  change Tree.branch (85 : Fin 175) _ = Tree.branch (85 : Fin 175) _
  apply congrArg (Tree.branch (85 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0487
  · rfl
  · rfl
  · rfl

theorem accepted0045 : B0045.accepted = true := by decide +kernel
theorem checked0045 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node0045 (maskNeeds ![1238242271318996484309909889, 226673591178292726072834, 33887720327816647763040260, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq0045]
  exact B0045.sound accepted0045
#print axioms checked0045

def B0544 : Block := .branch 163 ![385, 1538, 6148, 24584, 89203661359505371550386653293374621601595408, 393248, 748288849507353694807469898273653799753954862039104] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 832).pointIds 832), (.leaf 5 (Common.fact 387).pointIds 387), (.leaf 6 (Common.fact 833).pointIds 833)]
theorem treeEq0544 : B0544.tree = HexagonCover.NBand.M8500_8700.SplitData.node0544 := by
  change Tree.branch (163 : Fin 175) _ = Tree.branch (163 : Fin 175) _
  apply congrArg (Tree.branch (163 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0543 : Block := .branch 129 ![385, 1538, 6148, 2993155353253689176481146542238650902713866546864136, 89202980794771529673459726544159758065172496, 393248, 748288849540063337327745108074070683893333581365312] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), (.leaf 2 (Common.fact 322).pointIds 322), (.leaf 3 (Common.fact 831).pointIds 831), B0544, (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 6 (Common.fact 324).pointIds 324)]
theorem treeEq0543 : B0543.tree = HexagonCover.NBand.M8500_8700.SplitData.node0543 := by
  change Tree.branch (129 : Fin 175) _ = Tree.branch (129 : Fin 175) _
  apply congrArg (Tree.branch (129 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0544
  · rfl
  · rfl

def B0542 : Block := .branch 138 ![385, 1538, 6148, 2993155353253689176481146542238650902713866546864136, 89202980794771529673459726544159758065172496, 393248, 748288849540063337327745108074070683893333581365312] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), (.leaf 3 (Common.fact 830).pointIds 830), B0543, (.leaf 5 (Common.fact 333).pointIds 333), (.leaf 6 (Common.fact 334).pointIds 334)]
theorem treeEq0542 : B0542.tree = HexagonCover.NBand.M8500_8700.SplitData.node0542 := by
  change Tree.branch (138 : Fin 175) _ = Tree.branch (138 : Fin 175) _
  apply congrArg (Tree.branch (138 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0543
  · rfl
  · rfl

def B0541 : Block := .branch 165 ![385, 1538, 6148, 2993155353253689176481146542238650902713866546864136, 89202980794771529673459726544159758065172496, 393248, 748288849540063337327745108074070683893333581365312] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 829).pointIds 829), B0542, (.leaf 0 [] 0)]
theorem treeEq0541 : B0541.tree = HexagonCover.NBand.M8500_8700.SplitData.node0541 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0542
  · rfl

def B0540 : Block := .branch 167 ![385, 1538, 6148, 2993155353253689176481146542238650902713866546864136, 89202980794771529673459726544159758065172496, 393248, 748288849540063337327745108074070683893333581365312] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 828).pointIds 828), B0541, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq0540 : B0540.tree = HexagonCover.NBand.M8500_8700.SplitData.node0540 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0541
  · rfl

def B0539 : Block := .branch 146 ![385, 1538, 6148, 2993155353253689176481146542238650902713866546864136, 649037107316853453566312041250832, 393248, 748288849540063337327745108074070683893333581365312] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 347).pointIds 347), (.leaf 3 (Common.fact 827).pointIds 827), B0540, (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 0 [] 0)]
theorem treeEq0539 : B0539.tree = HexagonCover.NBand.M8500_8700.SplitData.node0539 := by
  change Tree.branch (146 : Fin 175) _ = Tree.branch (146 : Fin 175) _
  apply congrArg (Tree.branch (146 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0540
  · rfl
  · rfl

def B0538 : Block := .branch 160 ![385, 1538, 5986310706507378352962293084515080737290690255394820, 2993155353253689176481146542238650902713866546864136, 649037107316853453566312041250832, 393248, 748288849540063337327745108074070683893333581365312] ![(.leaf 0 (Common.fact 392).pointIds 392), B0539, (.leaf 2 (Common.fact 825).pointIds 825), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 826).pointIds 826)]
theorem treeEq0538 : B0538.tree = HexagonCover.NBand.M8500_8700.SplitData.node0538 := by
  change Tree.branch (160 : Fin 175) _ = Tree.branch (160 : Fin 175) _
  apply congrArg (Tree.branch (160 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0539
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0537 : Block := .branch 172 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 2993155353253689176481146542238650902713866546864136, 1329877032892232726357373372321595408, 393248, 748288849540063337327745108074070683893333581365312] ![(.leaf 0 (Common.fact 740).pointIds 740), (.leaf 1 (Common.fact 769).pointIds 769), B0538, (.leaf 3 (Common.fact 824).pointIds 824), (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 691).pointIds 691)]
theorem treeEq0537 : B0537.tree = HexagonCover.NBand.M8500_8700.SplitData.node0537 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0538
  · rfl
  · rfl
  · rfl
  · rfl

def B0536 : Block := .branch 171 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 4835703278458516698849288, 1329877032892232726357373372321595408, 393248, 748288849540063337327745108074070683893333581365312] ![(.leaf 0 (Common.fact 743).pointIds 743), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 818).pointIds 818), B0537, (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 692).pointIds 692)]
theorem treeEq0536 : B0536.tree = HexagonCover.NBand.M8500_8700.SplitData.node0536 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0537
  · rfl
  · rfl
  · rfl

def B0535 : Block := .branch 169 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 158461160731807133703786749960, 1329877032892232726357373372321595408, 1496577676626844588240573268701473812127674924400672, 11226641043207458473723333777829496119361600] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 775).pointIds 775), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 823).pointIds 823), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), B0536]
theorem treeEq0535 : B0535.tree = HexagonCover.NBand.M8500_8700.SplitData.node0535 := by
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
  · exact treeEq0536

def B0534 : Block := .branch 170 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 158461160731807133703786749960, 1329877032892232726357373372321595408, 393248, 11226641043207458473723333777829496119361600] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 773).pointIds 773), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 821).pointIds 821), (.leaf 4 (Common.fact 749).pointIds 749), B0535, (.leaf 6 (Common.fact 643).pointIds 643)]
theorem treeEq0534 : B0534.tree = HexagonCover.NBand.M8500_8700.SplitData.node0534 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0535
  · rfl

theorem accepted0534 : B0534.accepted = true := by decide +kernel
theorem checked0534 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node0534 (maskNeeds ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 158461160731807133703786749960, 1329877032892232726357373372321595408, 393248, 11226641043207458473723333777829496119361600]) := by
  rw [← treeEq0534]
  exact B0534.sound accepted0534
#print axioms checked0534

def Tip0523_0534 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node0534 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 158461160731807133703786749960, 1329877032892232726357373372321595408, 393248, 11226641043207458473723333777829496119361600] checked0534
def B0528 : Block := .branch 169 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 775).pointIds 775), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 823).pointIds 823), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq0528 : B0528.tree = HexagonCover.NBand.M8500_8700.SplitData.node0528 := by
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

def B0527 : Block := .branch 170 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 773).pointIds 773), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 821).pointIds 821), (.leaf 4 (Common.fact 749).pointIds 749), B0528, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq0527 : B0527.tree = HexagonCover.NBand.M8500_8700.SplitData.node0527 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0528
  · rfl

def B0526 : Block := .branch 171 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 680564734317250737715613698941498974216, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 743).pointIds 743), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 819).pointIds 819), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B0527]
theorem treeEq0526 : B0526.tree = HexagonCover.NBand.M8500_8700.SplitData.node0526 := by
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
  · exact treeEq0527

def B0533 : Block := .branch 169 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 775).pointIds 775), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 823).pointIds 823), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq0533 : B0533.tree = HexagonCover.NBand.M8500_8700.SplitData.node0533 := by
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

def B0532 : Block := .branch 170 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 773).pointIds 773), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 821).pointIds 821), (.leaf 4 (Common.fact 749).pointIds 749), B0533, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq0532 : B0532.tree = HexagonCover.NBand.M8500_8700.SplitData.node0532 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0533
  · rfl

def B0531 : Block := .branch 163 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 684553066866338991398914202356418707472, 233840261972944466912589573234605283144949207269408, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 618).pointIds 618), (.leaf 5 (Common.fact 387).pointIds 387), B0532]
theorem treeEq0531 : B0531.tree = HexagonCover.NBand.M8500_8700.SplitData.node0531 := by
  change Tree.branch (163 : Fin 175) _ = Tree.branch (163 : Fin 175) _
  apply congrArg (Tree.branch (163 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0532

def B0530 : Block := .branch 165 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 684553066866338991398914202356418707472, 187072209578355573530071658587684226515959365894176, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 617).pointIds 617), B0531, (.leaf 0 [] 0)]
theorem treeEq0530 : B0530.tree = HexagonCover.NBand.M8500_8700.SplitData.node0530 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0531
  · rfl

def B0529 : Block := .branch 167 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 684553066866338991398914202356418707472, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 616).pointIds 616), B0530, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq0529 : B0529.tree = HexagonCover.NBand.M8500_8700.SplitData.node0529 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0530
  · rfl

def B0525 : Block := .branch 129 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 475373810788864484077962551304, 3988333024462064472164987492882284560, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), (.leaf 2 (Common.fact 322).pointIds 322), B0526, B0529, (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 6 (Common.fact 324).pointIds 324)]
theorem treeEq0525 : B0525.tree = HexagonCover.NBand.M8500_8700.SplitData.node0525 := by
  change Tree.branch (129 : Fin 175) _ = Tree.branch (129 : Fin 175) _
  apply congrArg (Tree.branch (129 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0526
  · exact treeEq0529
  · rfl
  · rfl

def B0524 : Block := .branch 121 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 315).pointIds 315), (.leaf 1 (Common.fact 316).pointIds 316), (.leaf 2 (Common.fact 317).pointIds 317), (.leaf 3 (Common.fact 318).pointIds 318), B0525, (.leaf 5 (Common.fact 319).pointIds 319), Tip0523_0534]
theorem treeEq0524 : B0524.tree = HexagonCover.NBand.M8500_8700.SplitData.node0524 := by
  change Tree.branch (121 : Fin 175) _ = Tree.branch (121 : Fin 175) _
  apply congrArg (Tree.branch (121 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0525
  · rfl
  · rfl

def B0549 : Block := .branch 169 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 775).pointIds 775), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 823).pointIds 823), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq0549 : B0549.tree = HexagonCover.NBand.M8500_8700.SplitData.node0549 := by
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

def B0548 : Block := .branch 170 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 773).pointIds 773), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 821).pointIds 821), (.leaf 4 (Common.fact 749).pointIds 749), B0549, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq0548 : B0548.tree = HexagonCover.NBand.M8500_8700.SplitData.node0548 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0549
  · rfl

def B0547 : Block := .branch 163 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1994491030784690662809276902461767696, 233840261972944466912589573234605283144949207269408, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 387).pointIds 387), B0548]
theorem treeEq0547 : B0547.tree = HexagonCover.NBand.M8500_8700.SplitData.node0547 := by
  change Tree.branch (163 : Fin 175) _ = Tree.branch (163 : Fin 175) _
  apply congrArg (Tree.branch (163 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0548

def B0546 : Block := .branch 165 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1994491030784690662809276902461767696, 187072209578355573530071658587684226515959365894176, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 645).pointIds 645), B0547, (.leaf 0 [] 0)]
theorem treeEq0546 : B0546.tree = HexagonCover.NBand.M8500_8700.SplitData.node0546 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0547
  · rfl

def B0545 : Block := .branch 167 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1994491030784690662809276902461767696, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 644).pointIds 644), B0546, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq0545 : B0545.tree = HexagonCover.NBand.M8500_8700.SplitData.node0545 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0546
  · rfl

def B0523 : Block := .branch 119 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 310).pointIds 310), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), B0524, B0545, (.leaf 5 (Common.fact 313).pointIds 313), (.leaf 6 (Common.fact 314).pointIds 314)]
theorem treeEq0523 : B0523.tree = HexagonCover.NBand.M8500_8700.SplitData.node0523 := by
  change Tree.branch (119 : Fin 175) _ = Tree.branch (119 : Fin 175) _
  apply congrArg (Tree.branch (119 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0524
  · exact treeEq0545
  · rfl
  · rfl

theorem accepted0523 : B0523.accepted = true := by decide +kernel
theorem checked0523 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node0523 (maskNeeds ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq0523]
  exact B0523.sound accepted0523
#print axioms checked0523

def B0581 : Block := .branch 163 ![385, 1538, 6148, 24584, 89203661359505371550386653293374621601595408, 393248, 748288849507353694807469898273653799753954862039104] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 832).pointIds 832), (.leaf 5 (Common.fact 387).pointIds 387), (.leaf 6 (Common.fact 833).pointIds 833)]
theorem treeEq0581 : B0581.tree = HexagonCover.NBand.M8500_8700.SplitData.node0581 := by
  change Tree.branch (163 : Fin 175) _ = Tree.branch (163 : Fin 175) _
  apply congrArg (Tree.branch (163 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0580 : Block := .branch 129 ![385, 1538, 6148, 2993155353253689176481146542238650902713866546864136, 89202980794771529673459726544159758065172496, 393248, 748288849540063337327745108074070683893333581365312] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), (.leaf 2 (Common.fact 322).pointIds 322), (.leaf 3 (Common.fact 831).pointIds 831), B0581, (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 6 (Common.fact 324).pointIds 324)]
theorem treeEq0580 : B0580.tree = HexagonCover.NBand.M8500_8700.SplitData.node0580 := by
  change Tree.branch (129 : Fin 175) _ = Tree.branch (129 : Fin 175) _
  apply congrArg (Tree.branch (129 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0581
  · rfl
  · rfl

def B0579 : Block := .branch 138 ![385, 1538, 6148, 2993155353253689176481146542238650902713866546864136, 89202980794771529673459726544159758065172496, 393248, 748288849540063337327745108074070683893333581365312] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), (.leaf 3 (Common.fact 830).pointIds 830), B0580, (.leaf 5 (Common.fact 333).pointIds 333), (.leaf 6 (Common.fact 334).pointIds 334)]
theorem treeEq0579 : B0579.tree = HexagonCover.NBand.M8500_8700.SplitData.node0579 := by
  change Tree.branch (138 : Fin 175) _ = Tree.branch (138 : Fin 175) _
  apply congrArg (Tree.branch (138 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0580
  · rfl
  · rfl

def B0578 : Block := .branch 165 ![385, 1538, 6148, 2993155353253689176481146542238650902713866546864136, 89202980794771529673459726544159758065172496, 393248, 748288849540063337327745108074070683893333581365312] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 829).pointIds 829), B0579, (.leaf 0 [] 0)]
theorem treeEq0578 : B0578.tree = HexagonCover.NBand.M8500_8700.SplitData.node0578 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0579
  · rfl

def B0577 : Block := .branch 167 ![385, 1538, 6148, 2993155353253689176481146542238650902713866546864136, 89202980794771529673459726544159758065172496, 393248, 748288849540063337327745108074070683893333581365312] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 828).pointIds 828), B0578, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq0577 : B0577.tree = HexagonCover.NBand.M8500_8700.SplitData.node0577 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0578
  · rfl

def B0576 : Block := .branch 146 ![385, 1538, 6148, 2993155353253689176481146542238650902713866546864136, 649037107316853453566312041250832, 393248, 748288849540063337327745108074070683893333581365312] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 347).pointIds 347), (.leaf 3 (Common.fact 827).pointIds 827), B0577, (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 0 [] 0)]
theorem treeEq0576 : B0576.tree = HexagonCover.NBand.M8500_8700.SplitData.node0576 := by
  change Tree.branch (146 : Fin 175) _ = Tree.branch (146 : Fin 175) _
  apply congrArg (Tree.branch (146 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0577
  · rfl
  · rfl

def B0575 : Block := .branch 160 ![385, 1538, 5986310706507378352962293084515080737290690255394820, 2993155353253689176481146542238650902713866546864136, 649037107316853453566312041250832, 393248, 748288849540063347712338825143725940954326239805504] ![(.leaf 0 (Common.fact 392).pointIds 392), B0576, (.leaf 2 (Common.fact 825).pointIds 825), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 838).pointIds 838)]
theorem treeEq0575 : B0575.tree = HexagonCover.NBand.M8500_8700.SplitData.node0575 := by
  change Tree.branch (160 : Fin 175) _ = Tree.branch (160 : Fin 175) _
  apply congrArg (Tree.branch (160 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0576
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0574 : Block := .branch 172 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 2993155353253689176481146542238650902713866546864136, 1329877032892232726357373372321595408, 393248, 748288849540063347712338825143725940954326239805504] ![(.leaf 0 (Common.fact 740).pointIds 740), (.leaf 1 (Common.fact 769).pointIds 769), B0575, (.leaf 3 (Common.fact 824).pointIds 824), (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq0574 : B0574.tree = HexagonCover.NBand.M8500_8700.SplitData.node0574 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0575
  · rfl
  · rfl
  · rfl
  · rfl

def B0573 : Block := .branch 171 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 4835703278458516698849288, 1329877032892232726357373372321595408, 393248, 748288849540063347712338825143725940954326239805504] ![(.leaf 0 (Common.fact 743).pointIds 743), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 818).pointIds 818), B0574, (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 692).pointIds 692)]
theorem treeEq0573 : B0573.tree = HexagonCover.NBand.M8500_8700.SplitData.node0573 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0574
  · rfl
  · rfl
  · rfl

def B0572 : Block := .branch 169 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 158461160731807133703786749960, 1329877032892232726357373372321595408, 1496577676626844588240573268701473812127674924400672, 11226641053592052190792989034890488777801792] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 775).pointIds 775), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 823).pointIds 823), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), B0573]
theorem treeEq0572 : B0572.tree = HexagonCover.NBand.M8500_8700.SplitData.node0572 := by
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
  · exact treeEq0573

def B0571 : Block := .branch 170 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 158461160731807133703786749960, 1329877032892232726357373372321595408, 393248, 11226641053592052190792989034890488777801792] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 773).pointIds 773), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 821).pointIds 821), (.leaf 4 (Common.fact 749).pointIds 749), B0572, (.leaf 6 (Common.fact 837).pointIds 837)]
theorem treeEq0571 : B0571.tree = HexagonCover.NBand.M8500_8700.SplitData.node0571 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0572
  · rfl

theorem accepted0571 : B0571.accepted = true := by decide +kernel
theorem checked0571 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node0571 (maskNeeds ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 158461160731807133703786749960, 1329877032892232726357373372321595408, 393248, 11226641053592052190792989034890488777801792]) := by
  rw [← treeEq0571]
  exact B0571.sound accepted0571
#print axioms checked0571

end HexagonCover.NBand.M8500_8700.SplitTree.Run0006
