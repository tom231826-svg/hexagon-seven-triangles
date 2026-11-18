import HexagonCover.NBand.M8500_8700.SplitData
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8500_8700.SplitTree.Run0004
open OwnerTree HexagonCover.NBand.M8500_8700

abbrev Block := Chunk (n := 175) (Certificate := Fin 1173) (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck

def B0367 : Block := .branch 169 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 3367299783604329065772481548669487163363265418362944] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 775).pointIds 775), (.leaf 2 (Common.fact 776).pointIds 776), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 444).pointIds 444)]
theorem treeEq0367 : B0367.tree = HexagonCover.NBand.M8500_8700.SplitData.node0367 := by
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

def B0366 : Block := .branch 170 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 3367299783604329065772481548669487163363265418362944] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 773).pointIds 773), (.leaf 2 (Common.fact 774).pointIds 774), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B0367, (.leaf 6 (Common.fact 440).pointIds 440)]
theorem treeEq0366 : B0366.tree = HexagonCover.NBand.M8500_8700.SplitData.node0366 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0367
  · rfl

def B0365 : Block := .branch 171 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 5986310706855827496689809430367476432546391608287240, 1329227995784915872903807060280442896, 393248, 374144430350639889291335011266539539107915570348096] ![(.leaf 0 (Common.fact 743).pointIds 743), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 772).pointIds 772), (.leaf 3 (Common.fact 578).pointIds 578), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B0366]
theorem treeEq0365 : B0365.tree = HexagonCover.NBand.M8500_8700.SplitData.node0365 := by
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
  · exact treeEq0366

def B0364 : Block := .branch 172 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 393248, 374144430350639889291335011266539539107915570348096] ![(.leaf 0 (Common.fact 740).pointIds 740), (.leaf 1 (Common.fact 769).pointIds 769), (.leaf 2 (Common.fact 770).pointIds 770), B0365, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 452).pointIds 452)]
theorem treeEq0364 : B0364.tree = HexagonCover.NBand.M8500_8700.SplitData.node0364 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0365
  · rfl
  · rfl
  · rfl

def B0363 : Block := .branch 168 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 22300745198530623141535718272648361506373664, 11193928742231191694091171086075996839346240] ![(.leaf 0 (Common.fact 761).pointIds 761), (.leaf 1 (Common.fact 767).pointIds 767), (.leaf 2 (Common.fact 768).pointIds 768), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 517).pointIds 517), B0364]
theorem treeEq0363 : B0363.tree = HexagonCover.NBand.M8500_8700.SplitData.node0363 := by
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
  · exact treeEq0364

def B0369 : Block := .branch 171 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 5986310706855827496689650974042447903871204520386568, 1329227995784915872903807060280442896, 393248, 33451160333091799829611510330799020985286720] ![(.leaf 0 (Common.fact 743).pointIds 743), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 772).pointIds 772), (.leaf 3 (Common.fact 578).pointIds 578), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 567).pointIds 567)]
theorem treeEq0369 : B0369.tree = HexagonCover.NBand.M8500_8700.SplitData.node0369 := by
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

def B0368 : Block := .branch 172 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 348449143727357899236552655360504824356872, 1329227995784915872903807060280442896, 393248, 33451160333091799829611510330799020985286720] ![(.leaf 0 (Common.fact 740).pointIds 740), (.leaf 1 (Common.fact 769).pointIds 769), (.leaf 2 (Common.fact 770).pointIds 770), B0369, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 570).pointIds 570)]
theorem treeEq0368 : B0368.tree = HexagonCover.NBand.M8500_8700.SplitData.node0368 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0369
  · rfl
  · rfl
  · rfl

def B0362 : Block := .branch 144 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 340).pointIds 340), (.leaf 1 (Common.fact 341).pointIds 341), (.leaf 2 (Common.fact 342).pointIds 342), (.leaf 3 (Common.fact 343).pointIds 343), (.leaf 4 (Common.fact 344).pointIds 344), B0363, B0368]
theorem treeEq0362 : B0362.tree = HexagonCover.NBand.M8500_8700.SplitData.node0362 := by
  change Tree.branch (144 : Fin 175) _ = Tree.branch (144 : Fin 175) _
  apply congrArg (Tree.branch (144 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0363
  · exact treeEq0368

def B0375 : Block := .branch 169 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 3367299789179515365405137334053416731525355794858048] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 775).pointIds 775), (.leaf 2 (Common.fact 776).pointIds 776), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 586).pointIds 586)]
theorem treeEq0375 : B0375.tree = HexagonCover.NBand.M8500_8700.SplitData.node0375 := by
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

def B0374 : Block := .branch 170 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 3367299789179515365405137334053416731525355794858048] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 773).pointIds 773), (.leaf 2 (Common.fact 774).pointIds 774), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B0375, (.leaf 6 (Common.fact 583).pointIds 583)]
theorem treeEq0374 : B0374.tree = HexagonCover.NBand.M8500_8700.SplitData.node0374 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0375
  · rfl

def B0373 : Block := .branch 171 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 5986310706855827496689809430367476432546391608287240, 1329227995784915872903807060280442896, 393248, 374144435925826188923990796650469107270005946843200] ![(.leaf 0 (Common.fact 743).pointIds 743), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 772).pointIds 772), (.leaf 3 (Common.fact 578).pointIds 578), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B0374]
theorem treeEq0373 : B0373.tree = HexagonCover.NBand.M8500_8700.SplitData.node0373 := by
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
  · exact treeEq0374

def B0372 : Block := .branch 172 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 393248, 374144435925826188923990796650469107270005946843200] ![(.leaf 0 (Common.fact 740).pointIds 740), (.leaf 1 (Common.fact 769).pointIds 769), (.leaf 2 (Common.fact 770).pointIds 770), B0373, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 577).pointIds 577)]
theorem treeEq0372 : B0372.tree = HexagonCover.NBand.M8500_8700.SplitData.node0372 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0373
  · rfl
  · rfl
  · rfl

def B0371 : Block := .branch 168 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 5708990770823839524233143877797980545531379744, 16769115041863847479475100654238087215841344] ![(.leaf 0 (Common.fact 761).pointIds 761), (.leaf 1 (Common.fact 767).pointIds 767), (.leaf 2 (Common.fact 768).pointIds 768), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 574).pointIds 574), B0372]
theorem treeEq0371 : B0371.tree = HexagonCover.NBand.M8500_8700.SplitData.node0371 := by
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
  · exact treeEq0372

def B0370 : Block := .branch 152 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 16769157577159712596783033576064016186867776] ![(.leaf 0 (Common.fact 354).pointIds 354), (.leaf 1 (Common.fact 355).pointIds 355), (.leaf 2 (Common.fact 356).pointIds 356), (.leaf 3 (Common.fact 357).pointIds 357), (.leaf 4 (Common.fact 358).pointIds 358), B0371, (.leaf 6 (Common.fact 571).pointIds 571)]
theorem treeEq0370 : B0370.tree = HexagonCover.NBand.M8500_8700.SplitData.node0370 := by
  change Tree.branch (152 : Fin 175) _ = Tree.branch (152 : Fin 175) _
  apply congrArg (Tree.branch (152 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0371
  · rfl

def B0361 : Block := .branch 142 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), B0362, (.leaf 5 (Common.fact 339).pointIds 339), B0370]
theorem treeEq0361 : B0361.tree = HexagonCover.NBand.M8500_8700.SplitData.node0361 := by
  change Tree.branch (142 : Fin 175) _ = Tree.branch (142 : Fin 175) _
  apply congrArg (Tree.branch (142 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0362
  · rfl
  · exact treeEq0370

theorem accepted0361 : B0361.accepted = true := by decide +kernel
theorem checked0361 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node0361 (maskNeeds ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 11193971277527056811399104007901925810372672]) := by
  rw [← treeEq0361]
  exact B0361.sound accepted0361
#print axioms checked0361

def Tip0358_0361 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node0361 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 11193971277527056811399104007901925810372672] checked0361
def B0380 : Block := .branch 169 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 775).pointIds 775), (.leaf 2 (Common.fact 776).pointIds 776), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq0380 : B0380.tree = HexagonCover.NBand.M8500_8700.SplitData.node0380 := by
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

def B0379 : Block := .branch 170 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 773).pointIds 773), (.leaf 2 (Common.fact 774).pointIds 774), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B0380, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq0379 : B0379.tree = HexagonCover.NBand.M8500_8700.SplitData.node0379 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0380
  · rfl

def B0378 : Block := .branch 163 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 353894991474808894234635949102411261509648, 233840261972944466912589573234605283144949207269408, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 589).pointIds 589), (.leaf 5 (Common.fact 387).pointIds 387), B0379]
theorem treeEq0378 : B0378.tree = HexagonCover.NBand.M8500_8700.SplitData.node0378 := by
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
  · exact treeEq0379

def B0377 : Block := .branch 165 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 353894991474808894234635949102411261509648, 187072209578355573530071658587684226515959365894176, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 588).pointIds 588), B0378, (.leaf 0 [] 0)]
theorem treeEq0377 : B0377.tree = HexagonCover.NBand.M8500_8700.SplitData.node0377 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0378
  · rfl

def B0376 : Block := .branch 167 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 353894991474808894234635949102411261509648, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 587).pointIds 587), B0377, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq0376 : B0376.tree = HexagonCover.NBand.M8500_8700.SplitData.node0376 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0377
  · rfl

def B0360 : Block := .branch 138 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 475368975085586025561263726600, 1399242422655931853994122743132803207102480, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), Tip0358_0361, B0376, (.leaf 5 (Common.fact 333).pointIds 333), (.leaf 6 (Common.fact 334).pointIds 334)]
theorem treeEq0360 : B0360.tree = HexagonCover.NBand.M8500_8700.SplitData.node0360 := by
  change Tree.branch (138 : Fin 175) _ = Tree.branch (138 : Fin 175) _
  apply congrArg (Tree.branch (138 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0376
  · rfl
  · rfl

def B0386 : Block := .branch 169 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 3367299783609773583643216564084901157082173709746240] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 775).pointIds 775), (.leaf 2 (Common.fact 776).pointIds 776), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 615).pointIds 615)]
theorem treeEq0386 : B0386.tree = HexagonCover.NBand.M8500_8700.SplitData.node0386 := by
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

def B0385 : Block := .branch 170 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 3367299783609773583643216564084901157082173709746240] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 773).pointIds 773), (.leaf 2 (Common.fact 774).pointIds 774), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B0386, (.leaf 6 (Common.fact 612).pointIds 612)]
theorem treeEq0385 : B0385.tree = HexagonCover.NBand.M8500_8700.SplitData.node0385 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0386
  · rfl

def B0384 : Block := .branch 171 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 5986310706508058917696610320707907583751124496179208, 1329227995784915872903807060280442896, 393248, 374144430356084407162070026681953532826823861731392] ![(.leaf 0 (Common.fact 743).pointIds 743), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 772).pointIds 772), (.leaf 3 (Common.fact 608).pointIds 608), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B0385]
theorem treeEq0384 : B0384.tree = HexagonCover.NBand.M8500_8700.SplitData.node0384 := by
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
  · exact treeEq0385

def B0383 : Block := .branch 172 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 680564734317245902012335240424800149512, 1329227995784915872903807060280442896, 393248, 374144430356084407162070026681953532826823861731392] ![(.leaf 0 (Common.fact 740).pointIds 740), (.leaf 1 (Common.fact 769).pointIds 769), (.leaf 2 (Common.fact 770).pointIds 770), B0384, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 607).pointIds 607)]
theorem treeEq0383 : B0383.tree = HexagonCover.NBand.M8500_8700.SplitData.node0383 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0384
  · rfl
  · rfl
  · rfl

def B0382 : Block := .branch 168 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 680564734317245902012335240424800149512, 1329227995784915872903807060280442896, 5708990770823839524233143877797980545531379744, 11199373260101926709506585079794905130729536] ![(.leaf 0 (Common.fact 761).pointIds 761), (.leaf 1 (Common.fact 767).pointIds 767), (.leaf 2 (Common.fact 768).pointIds 768), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 574).pointIds 574), B0383]
theorem treeEq0382 : B0382.tree = HexagonCover.NBand.M8500_8700.SplitData.node0382 := by
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
  · exact treeEq0383

def B0381 : Block := .branch 152 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 680564734317245902012335240424800149512, 1393797904136159731261855295847582874566672, 393248, 11199415795397791826814518001620834101755968] ![(.leaf 0 (Common.fact 354).pointIds 354), (.leaf 1 (Common.fact 355).pointIds 355), (.leaf 2 (Common.fact 356).pointIds 356), (.leaf 3 (Common.fact 357).pointIds 357), (.leaf 4 (Common.fact 358).pointIds 358), B0382, (.leaf 6 (Common.fact 602).pointIds 602)]
theorem treeEq0381 : B0381.tree = HexagonCover.NBand.M8500_8700.SplitData.node0381 := by
  change Tree.branch (152 : Fin 175) _ = Tree.branch (152 : Fin 175) _
  apply congrArg (Tree.branch (152 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0382
  · rfl

def B0359 : Block := .branch 132 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 680564734317245902012335240424800149512, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B0360, (.leaf 5 (Common.fact 329).pointIds 329), B0381]
theorem treeEq0359 : B0359.tree = HexagonCover.NBand.M8500_8700.SplitData.node0359 := by
  change Tree.branch (132 : Fin 175) _ = Tree.branch (132 : Fin 175) _
  apply congrArg (Tree.branch (132 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0360
  · rfl
  · exact treeEq0381

def B0391 : Block := .branch 169 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 775).pointIds 775), (.leaf 2 (Common.fact 776).pointIds 776), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq0391 : B0391.tree = HexagonCover.NBand.M8500_8700.SplitData.node0391 := by
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

def B0390 : Block := .branch 170 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 773).pointIds 773), (.leaf 2 (Common.fact 774).pointIds 774), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B0391, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq0390 : B0390.tree = HexagonCover.NBand.M8500_8700.SplitData.node0390 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0391
  · rfl

def B0389 : Block := .branch 163 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 684553066866338991398914202356418707472, 233840261972944466912589573234605283144949207269408, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 618).pointIds 618), (.leaf 5 (Common.fact 387).pointIds 387), B0390]
theorem treeEq0389 : B0389.tree = HexagonCover.NBand.M8500_8700.SplitData.node0389 := by
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
  · exact treeEq0390

def B0388 : Block := .branch 165 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 684553066866338991398914202356418707472, 187072209578355573530071658587684226515959365894176, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 617).pointIds 617), B0389, (.leaf 0 [] 0)]
theorem treeEq0388 : B0388.tree = HexagonCover.NBand.M8500_8700.SplitData.node0388 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0389
  · rfl

def B0387 : Block := .branch 167 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 684553066866338991398914202356418707472, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 616).pointIds 616), B0388, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq0387 : B0387.tree = HexagonCover.NBand.M8500_8700.SplitData.node0387 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0388
  · rfl

def B0358 : Block := .branch 129 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 475368975085586025561263726600, 1393800563241188408410454557028015476408336, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), (.leaf 2 (Common.fact 322).pointIds 322), B0359, B0387, (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 6 (Common.fact 324).pointIds 324)]
theorem treeEq0358 : B0358.tree = HexagonCover.NBand.M8500_8700.SplitData.node0358 := by
  change Tree.branch (129 : Fin 175) _ = Tree.branch (129 : Fin 175) _
  apply congrArg (Tree.branch (129 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0359
  · exact treeEq0387
  · rfl
  · rfl

theorem accepted0358 : B0358.accepted = true := by decide +kernel
theorem checked0358 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node0358 (maskNeeds ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 475368975085586025561263726600, 1393800563241188408410454557028015476408336, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq0358]
  exact B0358.sound accepted0358
#print axioms checked0358

def B0420 : Block := .branch 169 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 3367299783604329065772481548669487163363265418362944] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 775).pointIds 775), (.leaf 2 (Common.fact 776).pointIds 776), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 444).pointIds 444)]
theorem treeEq0420 : B0420.tree = HexagonCover.NBand.M8500_8700.SplitData.node0420 := by
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

def B0419 : Block := .branch 170 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 3367299783604329065772481548669487163363265418362944] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 773).pointIds 773), (.leaf 2 (Common.fact 774).pointIds 774), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B0420, (.leaf 6 (Common.fact 440).pointIds 440)]
theorem treeEq0419 : B0419.tree = HexagonCover.NBand.M8500_8700.SplitData.node0419 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0420
  · rfl

def B0418 : Block := .branch 171 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 5986310706855827496689809430367476432546391608287240, 1329227995784915872903807060280442896, 393248, 374144430350639889291335011266539539107915570348096] ![(.leaf 0 (Common.fact 743).pointIds 743), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 772).pointIds 772), (.leaf 3 (Common.fact 578).pointIds 578), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B0419]
theorem treeEq0418 : B0418.tree = HexagonCover.NBand.M8500_8700.SplitData.node0418 := by
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
  · exact treeEq0419

def B0417 : Block := .branch 172 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 393248, 374144430350639889291335011266539539107915570348096] ![(.leaf 0 (Common.fact 740).pointIds 740), (.leaf 1 (Common.fact 769).pointIds 769), (.leaf 2 (Common.fact 770).pointIds 770), B0418, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 452).pointIds 452)]
theorem treeEq0417 : B0417.tree = HexagonCover.NBand.M8500_8700.SplitData.node0417 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0418
  · rfl
  · rfl
  · rfl

def B0416 : Block := .branch 168 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 22300745198530623141535718272648361506373664, 11193928742231191694091171086075996839346240] ![(.leaf 0 (Common.fact 761).pointIds 761), (.leaf 1 (Common.fact 767).pointIds 767), (.leaf 2 (Common.fact 768).pointIds 768), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 517).pointIds 517), B0417]
theorem treeEq0416 : B0416.tree = HexagonCover.NBand.M8500_8700.SplitData.node0416 := by
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
  · exact treeEq0417

def B0422 : Block := .branch 171 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 5986310706855827496689650974042447903871204520386568, 1329227995784915872903807060280442896, 393248, 33451160338284096688146337959329517314506816] ![(.leaf 0 (Common.fact 743).pointIds 743), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 772).pointIds 772), (.leaf 3 (Common.fact 578).pointIds 578), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 684).pointIds 684)]
theorem treeEq0422 : B0422.tree = HexagonCover.NBand.M8500_8700.SplitData.node0422 := by
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

def B0421 : Block := .branch 172 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 348449143727357899236552655360504824356872, 1329227995784915872903807060280442896, 393248, 33451160338284096688146337959329517314506816] ![(.leaf 0 (Common.fact 740).pointIds 740), (.leaf 1 (Common.fact 769).pointIds 769), (.leaf 2 (Common.fact 770).pointIds 770), B0422, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 683).pointIds 683)]
theorem treeEq0421 : B0421.tree = HexagonCover.NBand.M8500_8700.SplitData.node0421 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0422
  · rfl
  · rfl
  · rfl

def B0415 : Block := .branch 144 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 340).pointIds 340), (.leaf 1 (Common.fact 341).pointIds 341), (.leaf 2 (Common.fact 342).pointIds 342), (.leaf 3 (Common.fact 343).pointIds 343), (.leaf 4 (Common.fact 344).pointIds 344), B0416, B0421]
theorem treeEq0415 : B0415.tree = HexagonCover.NBand.M8500_8700.SplitData.node0415 := by
  change Tree.branch (144 : Fin 175) _ = Tree.branch (144 : Fin 175) _
  apply congrArg (Tree.branch (144 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0416
  · exact treeEq0421

def B0428 : Block := .branch 169 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 3367299789179515365405137334053416731525355794858048] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 775).pointIds 775), (.leaf 2 (Common.fact 776).pointIds 776), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 586).pointIds 586)]
theorem treeEq0428 : B0428.tree = HexagonCover.NBand.M8500_8700.SplitData.node0428 := by
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

def B0427 : Block := .branch 170 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 3367299789179515365405137334053416731525355794858048] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 773).pointIds 773), (.leaf 2 (Common.fact 774).pointIds 774), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B0428, (.leaf 6 (Common.fact 583).pointIds 583)]
theorem treeEq0427 : B0427.tree = HexagonCover.NBand.M8500_8700.SplitData.node0427 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0428
  · rfl

def B0426 : Block := .branch 171 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 5986310706855827496689809430367476432546391608287240, 1329227995784915872903807060280442896, 393248, 374144435925826188923990796650469107270005946843200] ![(.leaf 0 (Common.fact 743).pointIds 743), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 772).pointIds 772), (.leaf 3 (Common.fact 578).pointIds 578), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B0427]
theorem treeEq0426 : B0426.tree = HexagonCover.NBand.M8500_8700.SplitData.node0426 := by
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
  · exact treeEq0427

def B0425 : Block := .branch 172 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 393248, 374144435925826188923990796650469107270005946843200] ![(.leaf 0 (Common.fact 740).pointIds 740), (.leaf 1 (Common.fact 769).pointIds 769), (.leaf 2 (Common.fact 770).pointIds 770), B0426, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 577).pointIds 577)]
theorem treeEq0425 : B0425.tree = HexagonCover.NBand.M8500_8700.SplitData.node0425 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0426
  · rfl
  · rfl
  · rfl

def B0424 : Block := .branch 168 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 5708990770823839524233143877797980545531379744, 16769115041863847479475100654238087215841344] ![(.leaf 0 (Common.fact 761).pointIds 761), (.leaf 1 (Common.fact 767).pointIds 767), (.leaf 2 (Common.fact 768).pointIds 768), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 574).pointIds 574), B0425]
theorem treeEq0424 : B0424.tree = HexagonCover.NBand.M8500_8700.SplitData.node0424 := by
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
  · exact treeEq0425

def B0423 : Block := .branch 152 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 16769157582352009455317861204594512516087872] ![(.leaf 0 (Common.fact 354).pointIds 354), (.leaf 1 (Common.fact 355).pointIds 355), (.leaf 2 (Common.fact 356).pointIds 356), (.leaf 3 (Common.fact 357).pointIds 357), (.leaf 4 (Common.fact 358).pointIds 358), B0424, (.leaf 6 (Common.fact 685).pointIds 685)]
theorem treeEq0423 : B0423.tree = HexagonCover.NBand.M8500_8700.SplitData.node0423 := by
  change Tree.branch (152 : Fin 175) _ = Tree.branch (152 : Fin 175) _
  apply congrArg (Tree.branch (152 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0424
  · rfl

def B0414 : Block := .branch 142 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), B0415, (.leaf 5 (Common.fact 339).pointIds 339), B0423]
theorem treeEq0414 : B0414.tree = HexagonCover.NBand.M8500_8700.SplitData.node0414 := by
  change Tree.branch (142 : Fin 175) _ = Tree.branch (142 : Fin 175) _
  apply congrArg (Tree.branch (142 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0415
  · rfl
  · exact treeEq0423

theorem accepted0414 : B0414.accepted = true := by decide +kernel
theorem checked0414 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node0414 (maskNeeds ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 11193971282719353669933931636432422139592768]) := by
  rw [← treeEq0414]
  exact B0414.sound accepted0414
#print axioms checked0414

def Tip0411_0414 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node0414 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 11193971282719353669933931636432422139592768] checked0414
def B0433 : Block := .branch 169 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618506064983148595661900589669599936576] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 775).pointIds 775), (.leaf 2 (Common.fact 776).pointIds 776), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 688).pointIds 688)]
theorem treeEq0433 : B0433.tree = HexagonCover.NBand.M8500_8700.SplitData.node0433 := by
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

def B0432 : Block := .branch 170 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618506064983148595661900589669599936576] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 773).pointIds 773), (.leaf 2 (Common.fact 774).pointIds 774), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B0433, (.leaf 6 (Common.fact 686).pointIds 686)]
theorem treeEq0432 : B0432.tree = HexagonCover.NBand.M8500_8700.SplitData.node0432 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0433
  · rfl

def B0431 : Block := .branch 163 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 353894991474808894234635949102411261509648, 233840261972944466912589573234605283144949207269408, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 589).pointIds 589), (.leaf 5 (Common.fact 387).pointIds 387), B0432]
theorem treeEq0431 : B0431.tree = HexagonCover.NBand.M8500_8700.SplitData.node0431 := by
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
  · exact treeEq0432

def B0430 : Block := .branch 165 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 353894991474808894234635949102411261509648, 187072209578355573530071658587684226515959365894176, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 588).pointIds 588), B0431, (.leaf 0 [] 0)]
theorem treeEq0430 : B0430.tree = HexagonCover.NBand.M8500_8700.SplitData.node0430 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0431
  · rfl

def B0429 : Block := .branch 167 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 353894991474808894234635949102411261509648, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 587).pointIds 587), B0430, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq0429 : B0429.tree = HexagonCover.NBand.M8500_8700.SplitData.node0429 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0430
  · rfl

def B0413 : Block := .branch 138 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 475368975085586025561263726600, 1399242422655931853994122743132803207102480, 393248, 11226638389943763762426415598745871887892544] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), Tip0411_0414, B0429, (.leaf 5 (Common.fact 333).pointIds 333), (.leaf 6 (Common.fact 334).pointIds 334)]
theorem treeEq0413 : B0413.tree = HexagonCover.NBand.M8500_8700.SplitData.node0413 := by
  change Tree.branch (138 : Fin 175) _ = Tree.branch (138 : Fin 175) _
  apply congrArg (Tree.branch (138 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0429
  · rfl
  · rfl

def B0439 : Block := .branch 169 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 3367299783609773583643216564084901157082173709746240] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 775).pointIds 775), (.leaf 2 (Common.fact 776).pointIds 776), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 615).pointIds 615)]
theorem treeEq0439 : B0439.tree = HexagonCover.NBand.M8500_8700.SplitData.node0439 := by
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

def B0438 : Block := .branch 170 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 3367299783609773583643216564084901157082173709746240] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 773).pointIds 773), (.leaf 2 (Common.fact 774).pointIds 774), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B0439, (.leaf 6 (Common.fact 612).pointIds 612)]
theorem treeEq0438 : B0438.tree = HexagonCover.NBand.M8500_8700.SplitData.node0438 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0439
  · rfl

def B0437 : Block := .branch 171 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 5986310706508058917696610320707907583751124496179208, 1329227995784915872903807060280442896, 393248, 374144430356084407162070026681953532826823861731392] ![(.leaf 0 (Common.fact 743).pointIds 743), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 772).pointIds 772), (.leaf 3 (Common.fact 608).pointIds 608), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B0438]
theorem treeEq0437 : B0437.tree = HexagonCover.NBand.M8500_8700.SplitData.node0437 := by
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
  · exact treeEq0438

def B0436 : Block := .branch 172 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 680564734317245902012335240424800149512, 1329227995784915872903807060280442896, 393248, 374144430356084407162070026681953532826823861731392] ![(.leaf 0 (Common.fact 740).pointIds 740), (.leaf 1 (Common.fact 769).pointIds 769), (.leaf 2 (Common.fact 770).pointIds 770), B0437, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 607).pointIds 607)]
theorem treeEq0436 : B0436.tree = HexagonCover.NBand.M8500_8700.SplitData.node0436 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0437
  · rfl
  · rfl
  · rfl

def B0435 : Block := .branch 168 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 680564734317245902012335240424800149512, 1329227995784915872903807060280442896, 5708990770823839524233143877797980545531379744, 11199373260101926709506585079794905130729536] ![(.leaf 0 (Common.fact 761).pointIds 761), (.leaf 1 (Common.fact 767).pointIds 767), (.leaf 2 (Common.fact 768).pointIds 768), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 574).pointIds 574), B0436]
theorem treeEq0435 : B0435.tree = HexagonCover.NBand.M8500_8700.SplitData.node0435 := by
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
  · exact treeEq0436

def B0434 : Block := .branch 152 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 680564734317245902012335240424800149512, 1393797904136159731261855295847582874566672, 393248, 11199415800590088685349345630151330430976064] ![(.leaf 0 (Common.fact 354).pointIds 354), (.leaf 1 (Common.fact 355).pointIds 355), (.leaf 2 (Common.fact 356).pointIds 356), (.leaf 3 (Common.fact 357).pointIds 357), (.leaf 4 (Common.fact 358).pointIds 358), B0435, (.leaf 6 (Common.fact 689).pointIds 689)]
theorem treeEq0434 : B0434.tree = HexagonCover.NBand.M8500_8700.SplitData.node0434 := by
  change Tree.branch (152 : Fin 175) _ = Tree.branch (152 : Fin 175) _
  apply congrArg (Tree.branch (152 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0435
  · rfl

def B0412 : Block := .branch 132 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 680564734317245902012335240424800149512, 1393797904785196838578708749413894915719184, 393248, 11226638389943763762426415598745871887892544] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B0413, (.leaf 5 (Common.fact 329).pointIds 329), B0434]
theorem treeEq0412 : B0412.tree = HexagonCover.NBand.M8500_8700.SplitData.node0412 := by
  change Tree.branch (132 : Fin 175) _ = Tree.branch (132 : Fin 175) _
  apply congrArg (Tree.branch (132 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0413
  · rfl
  · exact treeEq0434

def B0444 : Block := .branch 169 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618506064983148595661900589669599936576] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 775).pointIds 775), (.leaf 2 (Common.fact 776).pointIds 776), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 688).pointIds 688)]
theorem treeEq0444 : B0444.tree = HexagonCover.NBand.M8500_8700.SplitData.node0444 := by
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

def B0443 : Block := .branch 170 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618506064983148595661900589669599936576] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 773).pointIds 773), (.leaf 2 (Common.fact 774).pointIds 774), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B0444, (.leaf 6 (Common.fact 686).pointIds 686)]
theorem treeEq0443 : B0443.tree = HexagonCover.NBand.M8500_8700.SplitData.node0443 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0444
  · rfl

def B0442 : Block := .branch 163 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 684553066866338991398914202356418707472, 233840261972944466912589573234605283144949207269408, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 618).pointIds 618), (.leaf 5 (Common.fact 387).pointIds 387), B0443]
theorem treeEq0442 : B0442.tree = HexagonCover.NBand.M8500_8700.SplitData.node0442 := by
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
  · exact treeEq0443

def B0441 : Block := .branch 165 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 684553066866338991398914202356418707472, 187072209578355573530071658587684226515959365894176, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 617).pointIds 617), B0442, (.leaf 0 [] 0)]
theorem treeEq0441 : B0441.tree = HexagonCover.NBand.M8500_8700.SplitData.node0441 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0442
  · rfl

def B0440 : Block := .branch 167 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 684553066866338991398914202356418707472, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 616).pointIds 616), B0441, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq0440 : B0440.tree = HexagonCover.NBand.M8500_8700.SplitData.node0440 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0441
  · rfl

def B0411 : Block := .branch 129 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 475368975085586025561263726600, 1393800563241188408410454557028015476408336, 393248, 11226638389943763762426415598745871887892544] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), (.leaf 2 (Common.fact 322).pointIds 322), B0412, B0440, (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 6 (Common.fact 324).pointIds 324)]
theorem treeEq0411 : B0411.tree = HexagonCover.NBand.M8500_8700.SplitData.node0411 := by
  change Tree.branch (129 : Fin 175) _ = Tree.branch (129 : Fin 175) _
  apply congrArg (Tree.branch (129 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0412
  · exact treeEq0440
  · rfl
  · rfl

theorem accepted0411 : B0411.accepted = true := by decide +kernel
theorem checked0411 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node0411 (maskNeeds ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 475368975085586025561263726600, 1393800563241188408410454557028015476408336, 393248, 11226638389943763762426415598745871887892544]) := by
  rw [← treeEq0411]
  exact B0411.sound accepted0411
#print axioms checked0411

end HexagonCover.NBand.M8500_8700.SplitTree.Run0004
