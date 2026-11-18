import HexagonCover.NBand.M8500_8700.SplitData
import HexagonCover.NBand.M8500_8700.SplitTree.Run0003
import HexagonCover.NBand.M8500_8700.SplitTree.Run0004
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8500_8700.SplitTree.Run0005
open OwnerTree HexagonCover.NBand.M8500_8700

abbrev Block := Chunk (n := 175) (Certificate := Fin 1173) (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck

def Tip0354_0358 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node0358 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 475368975085586025561263726600, 1393800563241188408410454557028015476408336, 393248, 11226638384751466903891587970215375558672448] HexagonCover.NBand.M8500_8700.SplitTree.Run0004.checked0358
def B0395 : Block := .branch 171 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 5986310706507379017576607879913888757764604012027912, 1329227995784915872903807060280442896, 393248, 748288849507353694807469898273653799753954862039104] ![(.leaf 0 (Common.fact 743).pointIds 743), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 772).pointIds 772), (.leaf 3 (Common.fact 636).pointIds 636), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 692).pointIds 692)]
theorem treeEq0395 : B0395.tree = HexagonCover.NBand.M8500_8700.SplitData.node0395 := by
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

def B0394 : Block := .branch 172 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 664614314805107993509253904315998216, 1329227995784915872903807060280442896, 393248, 748288849507353694807469898273653799753954862039104] ![(.leaf 0 (Common.fact 740).pointIds 740), (.leaf 1 (Common.fact 769).pointIds 769), (.leaf 2 (Common.fact 770).pointIds 770), B0395, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 691).pointIds 691)]
theorem treeEq0394 : B0394.tree = HexagonCover.NBand.M8500_8700.SplitData.node0394 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0395
  · rfl
  · rfl
  · rfl

def B0393 : Block := .branch 169 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 664614473261433022037929091403898888, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 11193931400687183263922916893690117400035392] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 775).pointIds 775), (.leaf 2 (Common.fact 776).pointIds 776), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), B0394]
theorem treeEq0393 : B0393.tree = HexagonCover.NBand.M8500_8700.SplitData.node0393 := by
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
  · exact treeEq0394

def B0392 : Block := .branch 170 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 664614473261433022037929091403898888, 1329227995784915872903807060280442896, 393248, 11193973935983048381230849815516046371061824] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 773).pointIds 773), (.leaf 2 (Common.fact 774).pointIds 774), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B0393, (.leaf 6 (Common.fact 643).pointIds 643)]
theorem treeEq0392 : B0392.tree = HexagonCover.NBand.M8500_8700.SplitData.node0392 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0393
  · rfl

def B0357 : Block := .branch 121 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 664614473261433022037929091403898888, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 315).pointIds 315), (.leaf 1 (Common.fact 316).pointIds 316), (.leaf 2 (Common.fact 317).pointIds 317), (.leaf 3 (Common.fact 318).pointIds 318), Tip0354_0358, (.leaf 5 (Common.fact 319).pointIds 319), B0392]
theorem treeEq0357 : B0357.tree = HexagonCover.NBand.M8500_8700.SplitData.node0357 := by
  change Tree.branch (121 : Fin 175) _ = Tree.branch (121 : Fin 175) _
  apply congrArg (Tree.branch (121 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0392

def B0400 : Block := .branch 169 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 775).pointIds 775), (.leaf 2 (Common.fact 776).pointIds 776), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq0400 : B0400.tree = HexagonCover.NBand.M8500_8700.SplitData.node0400 := by
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

def B0399 : Block := .branch 170 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 773).pointIds 773), (.leaf 2 (Common.fact 774).pointIds 774), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B0400, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq0399 : B0399.tree = HexagonCover.NBand.M8500_8700.SplitData.node0399 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0400
  · rfl

def B0398 : Block := .branch 163 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 1994491030784690662809276902461767696, 233840261972944466912589573234605283144949207269408, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 387).pointIds 387), B0399]
theorem treeEq0398 : B0398.tree = HexagonCover.NBand.M8500_8700.SplitData.node0398 := by
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
  · exact treeEq0399

def B0397 : Block := .branch 165 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 1994491030784690662809276902461767696, 187072209578355573530071658587684226515959365894176, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 645).pointIds 645), B0398, (.leaf 0 [] 0)]
theorem treeEq0397 : B0397.tree = HexagonCover.NBand.M8500_8700.SplitData.node0397 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0398
  · rfl

def B0396 : Block := .branch 167 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 1994491030784690662809276902461767696, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 644).pointIds 644), B0397, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq0396 : B0396.tree = HexagonCover.NBand.M8500_8700.SplitData.node0396 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0397
  · rfl

def B0356 : Block := .branch 119 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 475368975085586025561263726600, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 310).pointIds 310), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), B0357, B0396, (.leaf 5 (Common.fact 313).pointIds 313), (.leaf 6 (Common.fact 314).pointIds 314)]
theorem treeEq0356 : B0356.tree = HexagonCover.NBand.M8500_8700.SplitData.node0356 := by
  change Tree.branch (119 : Fin 175) _ = Tree.branch (119 : Fin 175) _
  apply congrArg (Tree.branch (119 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0357
  · exact treeEq0396
  · rfl
  · rfl

def B0402 : Block := .branch 171 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 5986310706507378353287128541114379032644229892431880, 1329227995784915872903807060280442896, 393248, 11193971298296244245538414522023911127253056] ![(.leaf 0 (Common.fact 743).pointIds 743), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 772).pointIds 772), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq0402 : B0402.tree = HexagonCover.NBand.M8500_8700.SplitData.node0402 := by
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

def B0401 : Block := .branch 172 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 324835466308483784133530196402184, 1329227995784915872903807060280442896, 393248, 11193971298296244245538414522023911127253056] ![(.leaf 0 (Common.fact 740).pointIds 740), (.leaf 1 (Common.fact 769).pointIds 769), (.leaf 2 (Common.fact 770).pointIds 770), B0402, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 666).pointIds 666)]
theorem treeEq0401 : B0401.tree = HexagonCover.NBand.M8500_8700.SplitData.node0401 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0402
  · rfl
  · rfl
  · rfl

def B0355 : Block := .branch 114 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 324993922633512312808717284302856, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448] ![B0356, (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 308).pointIds 308), (.leaf 5 (Common.fact 309).pointIds 309), B0401]
theorem treeEq0355 : B0355.tree = HexagonCover.NBand.M8500_8700.SplitData.node0355 := by
  change Tree.branch (114 : Fin 175) _ = Tree.branch (114 : Fin 175) _
  apply congrArg (Tree.branch (114 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0356
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0401

def B0406 : Block := .branch 169 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 775).pointIds 775), (.leaf 2 (Common.fact 776).pointIds 776), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq0406 : B0406.tree = HexagonCover.NBand.M8500_8700.SplitData.node0406 := by
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

def B0405 : Block := .branch 170 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 773).pointIds 773), (.leaf 2 (Common.fact 774).pointIds 774), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B0406, (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq0405 : B0405.tree = HexagonCover.NBand.M8500_8700.SplitData.node0405 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0406
  · rfl

def B0404 : Block := .branch 171 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 5986310706507378353287286997439407561319416980332552, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 743).pointIds 743), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 772).pointIds 772), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B0405]
theorem treeEq0404 : B0404.tree = HexagonCover.NBand.M8500_8700.SplitData.node0404 := by
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
  · exact treeEq0405

def B0403 : Block := .branch 172 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 740).pointIds 740), (.leaf 1 (Common.fact 769).pointIds 769), (.leaf 2 (Common.fact 770).pointIds 770), B0404, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq0403 : B0403.tree = HexagonCover.NBand.M8500_8700.SplitData.node0403 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0404
  · rfl
  · rfl
  · rfl

def B0354 : Block := .branch 113 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 324993922633512312808717284302856, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448] ![B0355, (.leaf 1 (Common.fact 300).pointIds 300), (.leaf 2 (Common.fact 301).pointIds 301), (.leaf 3 (Common.fact 302).pointIds 302), (.leaf 4 (Common.fact 303).pointIds 303), (.leaf 5 (Common.fact 304).pointIds 304), B0403]
theorem treeEq0354 : B0354.tree = HexagonCover.NBand.M8500_8700.SplitData.node0354 := by
  change Tree.branch (113 : Fin 175) _ = Tree.branch (113 : Fin 175) _
  apply congrArg (Tree.branch (113 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0355
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0403

theorem accepted0354 : B0354.accepted = true := by decide +kernel
theorem checked0354 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node0354 (maskNeeds ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 324993922633512312808717284302856, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq0354]
  exact B0354.sound accepted0354
#print axioms checked0354

def Tip0353_0411 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node0411 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 475368975085586025561263726600, 1393800563241188408410454557028015476408336, 393248, 11226638389943763762426415598745871887892544] HexagonCover.NBand.M8500_8700.SplitTree.Run0004.checked0411
def Tip0353_0354 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node0354 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 324993922633512312808717284302856, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448] checked0354
def B0448 : Block := .branch 171 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 5986310706507379017576607879913888757764604012027912, 1329227995784915872903807060280442896, 393248, 748288849507353694807469898273653799753954862039104] ![(.leaf 0 (Common.fact 743).pointIds 743), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 772).pointIds 772), (.leaf 3 (Common.fact 636).pointIds 636), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 692).pointIds 692)]
theorem treeEq0448 : B0448.tree = HexagonCover.NBand.M8500_8700.SplitData.node0448 := by
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

def B0447 : Block := .branch 172 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 664614314805107993509253904315998216, 1329227995784915872903807060280442896, 393248, 748288849507353694807469898273653799753954862039104] ![(.leaf 0 (Common.fact 740).pointIds 740), (.leaf 1 (Common.fact 769).pointIds 769), (.leaf 2 (Common.fact 770).pointIds 770), B0448, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 691).pointIds 691)]
theorem treeEq0447 : B0447.tree = HexagonCover.NBand.M8500_8700.SplitData.node0447 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0448
  · rfl
  · rfl
  · rfl

def B0446 : Block := .branch 169 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 664614473261433022037929091403898888, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 11193931400687183263922916893690117400035392] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 775).pointIds 775), (.leaf 2 (Common.fact 776).pointIds 776), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), B0447]
theorem treeEq0446 : B0446.tree = HexagonCover.NBand.M8500_8700.SplitData.node0446 := by
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
  · exact treeEq0447

def B0445 : Block := .branch 170 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 664614473261433022037929091403898888, 1329227995784915872903807060280442896, 393248, 11193973941175345239765677444046542700281920] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 773).pointIds 773), (.leaf 2 (Common.fact 774).pointIds 774), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B0446, (.leaf 6 (Common.fact 690).pointIds 690)]
theorem treeEq0445 : B0445.tree = HexagonCover.NBand.M8500_8700.SplitData.node0445 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0446
  · rfl

def B0410 : Block := .branch 121 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 664614473261433022037929091403898888, 1393797904785196838578708749413894915719184, 393248, 11226638389943763762426415598745871887892544] ![(.leaf 0 (Common.fact 315).pointIds 315), (.leaf 1 (Common.fact 316).pointIds 316), (.leaf 2 (Common.fact 317).pointIds 317), (.leaf 3 (Common.fact 318).pointIds 318), Tip0353_0411, (.leaf 5 (Common.fact 319).pointIds 319), B0445]
theorem treeEq0410 : B0410.tree = HexagonCover.NBand.M8500_8700.SplitData.node0410 := by
  change Tree.branch (121 : Fin 175) _ = Tree.branch (121 : Fin 175) _
  apply congrArg (Tree.branch (121 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0445

def B0453 : Block := .branch 169 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618506064983148595661900589669599936576] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 775).pointIds 775), (.leaf 2 (Common.fact 776).pointIds 776), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 688).pointIds 688)]
theorem treeEq0453 : B0453.tree = HexagonCover.NBand.M8500_8700.SplitData.node0453 := by
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

def B0452 : Block := .branch 170 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618506064983148595661900589669599936576] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 773).pointIds 773), (.leaf 2 (Common.fact 774).pointIds 774), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B0453, (.leaf 6 (Common.fact 686).pointIds 686)]
theorem treeEq0452 : B0452.tree = HexagonCover.NBand.M8500_8700.SplitData.node0452 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0453
  · rfl

def B0451 : Block := .branch 163 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 1994491030784690662809276902461767696, 233840261972944466912589573234605283144949207269408, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 387).pointIds 387), B0452]
theorem treeEq0451 : B0451.tree = HexagonCover.NBand.M8500_8700.SplitData.node0451 := by
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
  · exact treeEq0452

def B0450 : Block := .branch 165 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 1994491030784690662809276902461767696, 187072209578355573530071658587684226515959365894176, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 645).pointIds 645), B0451, (.leaf 0 [] 0)]
theorem treeEq0450 : B0450.tree = HexagonCover.NBand.M8500_8700.SplitData.node0450 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0451
  · rfl

def B0449 : Block := .branch 167 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 1994491030784690662809276902461767696, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 644).pointIds 644), B0450, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq0449 : B0449.tree = HexagonCover.NBand.M8500_8700.SplitData.node0449 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0450
  · rfl

def B0409 : Block := .branch 119 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 475368975085586025561263726600, 1393797904785196838578708749413894915719184, 393248, 11226638389943763762426415598745871887892544] ![(.leaf 0 (Common.fact 310).pointIds 310), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), B0410, B0449, (.leaf 5 (Common.fact 313).pointIds 313), (.leaf 6 (Common.fact 314).pointIds 314)]
theorem treeEq0409 : B0409.tree = HexagonCover.NBand.M8500_8700.SplitData.node0409 := by
  change Tree.branch (119 : Fin 175) _ = Tree.branch (119 : Fin 175) _
  apply congrArg (Tree.branch (119 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0410
  · exact treeEq0449
  · rfl
  · rfl

def B0455 : Block := .branch 171 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 5986310706507378353287128541114379032644229892431880, 1329227995784915872903807060280442896, 393248, 11193971298296244245538414522023911127253056] ![(.leaf 0 (Common.fact 743).pointIds 743), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 772).pointIds 772), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq0455 : B0455.tree = HexagonCover.NBand.M8500_8700.SplitData.node0455 := by
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

def B0454 : Block := .branch 172 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 324835466308483784133530196402184, 1329227995784915872903807060280442896, 393248, 11193971298296244245538414522023911127253056] ![(.leaf 0 (Common.fact 740).pointIds 740), (.leaf 1 (Common.fact 769).pointIds 769), (.leaf 2 (Common.fact 770).pointIds 770), B0455, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 666).pointIds 666)]
theorem treeEq0454 : B0454.tree = HexagonCover.NBand.M8500_8700.SplitData.node0454 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0455
  · rfl
  · rfl
  · rfl

def B0408 : Block := .branch 114 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 324993922633512312808717284302856, 1393797904785196838578708749413894915719184, 393248, 11226638389943763762426415598745871887892544] ![B0409, (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 308).pointIds 308), (.leaf 5 (Common.fact 309).pointIds 309), B0454]
theorem treeEq0408 : B0408.tree = HexagonCover.NBand.M8500_8700.SplitData.node0408 := by
  change Tree.branch (114 : Fin 175) _ = Tree.branch (114 : Fin 175) _
  apply congrArg (Tree.branch (114 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0409
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0454

def B0459 : Block := .branch 169 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 775).pointIds 775), (.leaf 2 (Common.fact 776).pointIds 776), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq0459 : B0459.tree = HexagonCover.NBand.M8500_8700.SplitData.node0459 := by
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

def B0458 : Block := .branch 170 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 773).pointIds 773), (.leaf 2 (Common.fact 774).pointIds 774), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B0459, (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq0458 : B0458.tree = HexagonCover.NBand.M8500_8700.SplitData.node0458 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0459
  · rfl

def B0457 : Block := .branch 171 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 5986310706507378353287286997439407561319416980332552, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 743).pointIds 743), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 772).pointIds 772), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B0458]
theorem treeEq0457 : B0457.tree = HexagonCover.NBand.M8500_8700.SplitData.node0457 := by
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
  · exact treeEq0458

def B0456 : Block := .branch 172 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 740).pointIds 740), (.leaf 1 (Common.fact 769).pointIds 769), (.leaf 2 (Common.fact 770).pointIds 770), B0457, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq0456 : B0456.tree = HexagonCover.NBand.M8500_8700.SplitData.node0456 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0457
  · rfl
  · rfl
  · rfl

def B0407 : Block := .branch 113 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 324993922633512312808717284302856, 1393797904785196838578708749413894915719184, 393248, 11226638389943763762426415598745871887892544] ![B0408, (.leaf 1 (Common.fact 300).pointIds 300), (.leaf 2 (Common.fact 301).pointIds 301), (.leaf 3 (Common.fact 302).pointIds 302), (.leaf 4 (Common.fact 303).pointIds 303), (.leaf 5 (Common.fact 304).pointIds 304), B0456]
theorem treeEq0407 : B0407.tree = HexagonCover.NBand.M8500_8700.SplitData.node0407 := by
  change Tree.branch (113 : Fin 175) _ = Tree.branch (113 : Fin 175) _
  apply congrArg (Tree.branch (113 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0408
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0456

def B0353 : Block := .branch 112 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 324993922633512312808717284302856, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448] ![Tip0353_0354, (.leaf 1 (Common.fact 295).pointIds 295), (.leaf 2 (Common.fact 296).pointIds 296), (.leaf 3 (Common.fact 297).pointIds 297), (.leaf 4 (Common.fact 298).pointIds 298), (.leaf 5 (Common.fact 299).pointIds 299), B0407]
theorem treeEq0353 : B0353.tree = HexagonCover.NBand.M8500_8700.SplitData.node0353 := by
  change Tree.branch (112 : Fin 175) _ = Tree.branch (112 : Fin 175) _
  apply congrArg (Tree.branch (112 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0407

theorem accepted0353 : B0353.accepted = true := by decide +kernel
theorem checked0353 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node0353 (maskNeeds ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 324993922633512312808717284302856, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq0353]
  exact B0353.sound accepted0353
#print axioms checked0353

def Tip0349_0353 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node0353 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 324993922633512312808717284302856, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448] checked0353
def B0461 : Block := .branch 168 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 11193971278176093918715957461468237851525184] ![(.leaf 0 (Common.fact 761).pointIds 761), (.leaf 1 (Common.fact 767).pointIds 767), (.leaf 2 (Common.fact 768).pointIds 768), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 765).pointIds 765), (.leaf 6 (Common.fact 706).pointIds 706)]
theorem treeEq0461 : B0461.tree = HexagonCover.NBand.M8500_8700.SplitData.node0461 := by
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

def B0460 : Block := .branch 170 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 11193971278176093918715957461468237851525184] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 773).pointIds 773), (.leaf 2 (Common.fact 774).pointIds 774), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B0461, (.leaf 6 (Common.fact 760).pointIds 760)]
theorem treeEq0460 : B0460.tree = HexagonCover.NBand.M8500_8700.SplitData.node0460 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0461
  · rfl

def B0352 : Block := .branch 109 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 325073150796026577146310828253192, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 290).pointIds 290), (.leaf 1 (Common.fact 291).pointIds 291), (.leaf 2 (Common.fact 292).pointIds 292), (.leaf 3 (Common.fact 293).pointIds 293), Tip0349_0353, (.leaf 5 (Common.fact 294).pointIds 294), B0460]
theorem treeEq0352 : B0352.tree = HexagonCover.NBand.M8500_8700.SplitData.node0352 := by
  change Tree.branch (109 : Fin 175) _ = Tree.branch (109 : Fin 175) _
  apply congrArg (Tree.branch (109 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0460

def B0466 : Block := .branch 169 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 775).pointIds 775), (.leaf 2 (Common.fact 776).pointIds 776), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq0466 : B0466.tree = HexagonCover.NBand.M8500_8700.SplitData.node0466 := by
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

def B0465 : Block := .branch 170 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 773).pointIds 773), (.leaf 2 (Common.fact 774).pointIds 774), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B0466, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq0465 : B0465.tree = HexagonCover.NBand.M8500_8700.SplitData.node0465 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0466
  · rfl

def B0464 : Block := .branch 163 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 1329552514338574299630590216301019152, 233840261972944466912589573234605283144949207269408, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 709).pointIds 709), (.leaf 5 (Common.fact 387).pointIds 387), B0465]
theorem treeEq0464 : B0464.tree = HexagonCover.NBand.M8500_8700.SplitData.node0464 := by
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
  · exact treeEq0465

def B0463 : Block := .branch 165 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 1329552514338574299630590216301019152, 187072209578355573530071658587684226515959365894176, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 708).pointIds 708), B0464, (.leaf 0 [] 0)]
theorem treeEq0463 : B0463.tree = HexagonCover.NBand.M8500_8700.SplitData.node0463 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0464
  · rfl

def B0462 : Block := .branch 167 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 1329552514338574299630590216301019152, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 707).pointIds 707), B0463, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq0462 : B0462.tree = HexagonCover.NBand.M8500_8700.SplitData.node0462 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0463
  · rfl

def B0351 : Block := .branch 108 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 554597137599850363154807676936, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), B0352, B0462, (.leaf 5 (Common.fact 288).pointIds 288), (.leaf 6 (Common.fact 289).pointIds 289)]
theorem treeEq0351 : B0351.tree = HexagonCover.NBand.M8500_8700.SplitData.node0351 := by
  change Tree.branch (108 : Fin 175) _ = Tree.branch (108 : Fin 175) _
  apply congrArg (Tree.branch (108 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0352
  · exact treeEq0462
  · rfl
  · rfl

def B0468 : Block := .branch 171 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 5986310706507378352962609987455952305861073871855624, 1329227995784915872903807060280442896, 393248, 11193971277528324461999332237303422513578048] ![(.leaf 0 (Common.fact 743).pointIds 743), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 772).pointIds 772), (.leaf 3 (Common.fact 766).pointIds 766), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 726).pointIds 726)]
theorem treeEq0468 : B0468.tree = HexagonCover.NBand.M8500_8700.SplitData.node0468 := by
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

def B0467 : Block := .branch 172 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 316912650057057350374175825928, 1329227995784915872903807060280442896, 393248, 11193971277528324461999332237303422513578048] ![(.leaf 0 (Common.fact 740).pointIds 740), (.leaf 1 (Common.fact 769).pointIds 769), (.leaf 2 (Common.fact 770).pointIds 770), B0468, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 728).pointIds 728)]
theorem treeEq0467 : B0467.tree = HexagonCover.NBand.M8500_8700.SplitData.node0467 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0468
  · rfl
  · rfl
  · rfl

def B0350 : Block := .branch 100 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 554597137599850363154807676936, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448] ![B0351, (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 281).pointIds 281), (.leaf 3 (Common.fact 282).pointIds 282), (.leaf 4 (Common.fact 283).pointIds 283), (.leaf 5 (Common.fact 284).pointIds 284), B0467]
theorem treeEq0350 : B0350.tree = HexagonCover.NBand.M8500_8700.SplitData.node0350 := by
  change Tree.branch (100 : Fin 175) _ = Tree.branch (100 : Fin 175) _
  apply congrArg (Tree.branch (100 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0351
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0467

def B0473 : Block := .branch 169 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 775).pointIds 775), (.leaf 2 (Common.fact 776).pointIds 776), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq0473 : B0473.tree = HexagonCover.NBand.M8500_8700.SplitData.node0473 := by
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

def B0472 : Block := .branch 170 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 773).pointIds 773), (.leaf 2 (Common.fact 774).pointIds 774), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B0473, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq0472 : B0472.tree = HexagonCover.NBand.M8500_8700.SplitData.node0472 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0473
  · rfl

def B0471 : Block := .branch 163 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 1329228312697565929961157434456244240, 233840261972944466912589573234605283144949207269408, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 731).pointIds 731), (.leaf 5 (Common.fact 387).pointIds 387), B0472]
theorem treeEq0471 : B0471.tree = HexagonCover.NBand.M8500_8700.SplitData.node0471 := by
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
  · exact treeEq0472

def B0470 : Block := .branch 165 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 1329228312697565929961157434456244240, 187072209578355573530071658587684226515959365894176, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 730).pointIds 730), B0471, (.leaf 0 [] 0)]
theorem treeEq0470 : B0470.tree = HexagonCover.NBand.M8500_8700.SplitData.node0470 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0471
  · rfl

def B0469 : Block := .branch 167 ![1238242271318996484309909889, 226673591178292726072834, 362677745884388752411858948, 158456325028528675187087925256, 1329228312697565929961157434456244240, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 729).pointIds 729), B0470, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq0469 : B0469.tree = HexagonCover.NBand.M8500_8700.SplitData.node0469 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0470
  · rfl

def B0349 : Block := .branch 98 ![1238242271318996484309909889, 226673591178292726072834, 362677764331132826121410564, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 275).pointIds 275), (.leaf 1 (Common.fact 276).pointIds 276), (.leaf 2 (Common.fact 277).pointIds 277), B0350, B0469, (.leaf 5 (Common.fact 278).pointIds 278), (.leaf 6 (Common.fact 279).pointIds 279)]
theorem treeEq0349 : B0349.tree = HexagonCover.NBand.M8500_8700.SplitData.node0349 := by
  change Tree.branch (98 : Fin 175) _ = Tree.branch (98 : Fin 175) _
  apply congrArg (Tree.branch (98 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0350
  · exact treeEq0469
  · rfl
  · rfl

theorem accepted0349 : B0349.accepted = true := by decide +kernel
theorem checked0349 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node0349 (maskNeeds ![1238242271318996484309909889, 226673591178292726072834, 362677764331132826121410564, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq0349]
  exact B0349.sound accepted0349
#print axioms checked0349

def Tip0048_0317 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node0317 ![1268888842499548397981013115265, 928455029464035755930158594, 130601767450242908029982724, 325073150796026577146310828253192, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] HexagonCover.NBand.M8500_8700.SplitTree.Run0003.checked0317
def Tip0048_0049 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node0049 ![618970020221402689566671233, 309636125548797447127434754, 130601785896986981739534340, 79228162514264337593543974920, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448] HexagonCover.NBand.M8500_8700.SplitTree.Run0003.checked0049
def B0340 : Block := .branch 169 ![1238242271318996484309909889, 928455029464035755930158594, 130601767450242908029982724, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 752).pointIds 752), (.leaf 2 (Common.fact 490).pointIds 490), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq0340 : B0340.tree = HexagonCover.NBand.M8500_8700.SplitData.node0340 := by
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

def B0339 : Block := .branch 170 ![1238242271318996484309909889, 928455029464035755930158594, 130601767450242908029982724, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 747).pointIds 747), (.leaf 2 (Common.fact 487).pointIds 487), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B0340, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq0339 : B0339.tree = HexagonCover.NBand.M8500_8700.SplitData.node0339 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0340
  · rfl

def B0338 : Block := .branch 163 ![1238242271318996484309909889, 928455029464035755930158594, 130601767450242908029982724, 158456325028528675187087925256, 1329552514338574299630590216301019152, 233840261972944466912589573234605283144949207269408, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 709).pointIds 709), (.leaf 5 (Common.fact 387).pointIds 387), B0339]
theorem treeEq0338 : B0338.tree = HexagonCover.NBand.M8500_8700.SplitData.node0338 := by
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
  · exact treeEq0339

def B0337 : Block := .branch 165 ![1238242271318996484309909889, 928455029464035755930158594, 130601767450242908029982724, 158456325028528675187087925256, 1329552514338574299630590216301019152, 187072209578355573530071658587684226515959365894176, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 708).pointIds 708), B0338, (.leaf 0 [] 0)]
theorem treeEq0337 : B0337.tree = HexagonCover.NBand.M8500_8700.SplitData.node0337 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0338
  · rfl

def B0336 : Block := .branch 167 ![1238242271318996484309909889, 928455029464035755930158594, 130601767450242908029982724, 158456325028528675187087925256, 1329552514338574299630590216301019152, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 707).pointIds 707), B0337, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq0336 : B0336.tree = HexagonCover.NBand.M8500_8700.SplitData.node0336 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0337
  · rfl

def B0316 : Block := .branch 108 ![1268888842499548397981013115265, 928455029464035755930158594, 130601767450242908029982724, 554597137599850363154807676936, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), Tip0048_0317, B0336, (.leaf 5 (Common.fact 288).pointIds 288), (.leaf 6 (Common.fact 289).pointIds 289)]
theorem treeEq0316 : B0316.tree = HexagonCover.NBand.M8500_8700.SplitData.node0316 := by
  change Tree.branch (108 : Fin 175) _ = Tree.branch (108 : Fin 175) _
  apply congrArg (Tree.branch (108 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0336
  · rfl
  · rfl

def B0342 : Block := .branch 171 ![1238242271318996484309909889, 928455029464035755930158594, 130601767450242908029982724, 5986310706507378352962609987455952305861073871855624, 1329227995784915872903807060280442896, 393248, 11193971277528324461999332237303422513578048] ![(.leaf 0 (Common.fact 743).pointIds 743), (.leaf 1 (Common.fact 744).pointIds 744), (.leaf 2 (Common.fact 478).pointIds 478), (.leaf 3 (Common.fact 766).pointIds 766), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 726).pointIds 726)]
theorem treeEq0342 : B0342.tree = HexagonCover.NBand.M8500_8700.SplitData.node0342 := by
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

def B0341 : Block := .branch 172 ![1238242271318996484309909889, 928455029464035755930158594, 130601767450242908029982724, 316912650057057350374175825928, 1329227995784915872903807060280442896, 393248, 11193971277528324461999332237303422513578048] ![(.leaf 0 (Common.fact 740).pointIds 740), (.leaf 1 (Common.fact 741).pointIds 741), (.leaf 2 (Common.fact 480).pointIds 480), B0342, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 728).pointIds 728)]
theorem treeEq0341 : B0341.tree = HexagonCover.NBand.M8500_8700.SplitData.node0341 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0342
  · rfl
  · rfl
  · rfl

def B0315 : Block := .branch 100 ![1238242271318996484309909889, 928455029464035755930158594, 130601767450242908029982724, 554597137599850363154807676936, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![B0316, (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 281).pointIds 281), (.leaf 3 (Common.fact 282).pointIds 282), (.leaf 4 (Common.fact 283).pointIds 283), (.leaf 5 (Common.fact 284).pointIds 284), B0341]
theorem treeEq0315 : B0315.tree = HexagonCover.NBand.M8500_8700.SplitData.node0315 := by
  change Tree.branch (100 : Fin 175) _ = Tree.branch (100 : Fin 175) _
  apply congrArg (Tree.branch (100 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0316
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0341

def B0347 : Block := .branch 169 ![1238242271318996484309909889, 928455029464035755930158594, 130601767450242908029982724, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 752).pointIds 752), (.leaf 2 (Common.fact 490).pointIds 490), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq0347 : B0347.tree = HexagonCover.NBand.M8500_8700.SplitData.node0347 := by
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

def B0346 : Block := .branch 170 ![1238242271318996484309909889, 928455029464035755930158594, 130601767450242908029982724, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 747).pointIds 747), (.leaf 2 (Common.fact 487).pointIds 487), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B0347, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq0346 : B0346.tree = HexagonCover.NBand.M8500_8700.SplitData.node0346 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0347
  · rfl

def B0345 : Block := .branch 163 ![1238242271318996484309909889, 928455029464035755930158594, 130601767450242908029982724, 158456325028528675187087925256, 1329228312697565929961157434456244240, 233840261972944466912589573234605283144949207269408, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 731).pointIds 731), (.leaf 5 (Common.fact 387).pointIds 387), B0346]
theorem treeEq0345 : B0345.tree = HexagonCover.NBand.M8500_8700.SplitData.node0345 := by
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
  · exact treeEq0346

def B0344 : Block := .branch 165 ![1238242271318996484309909889, 928455029464035755930158594, 130601767450242908029982724, 158456325028528675187087925256, 1329228312697565929961157434456244240, 187072209578355573530071658587684226515959365894176, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 730).pointIds 730), B0345, (.leaf 0 [] 0)]
theorem treeEq0344 : B0344.tree = HexagonCover.NBand.M8500_8700.SplitData.node0344 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0345
  · rfl

def B0343 : Block := .branch 167 ![1238242271318996484309909889, 928455029464035755930158594, 130601767450242908029982724, 158456325028528675187087925256, 1329228312697565929961157434456244240, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 729).pointIds 729), B0344, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq0343 : B0343.tree = HexagonCover.NBand.M8500_8700.SplitData.node0343 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0344
  · rfl

def B0314 : Block := .branch 98 ![1238242271318996484309909889, 928455029464035755930158594, 130601785896986981739534340, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 275).pointIds 275), (.leaf 1 (Common.fact 276).pointIds 276), (.leaf 2 (Common.fact 277).pointIds 277), B0315, B0343, (.leaf 5 (Common.fact 278).pointIds 278), (.leaf 6 (Common.fact 279).pointIds 279)]
theorem treeEq0314 : B0314.tree = HexagonCover.NBand.M8500_8700.SplitData.node0314 := by
  change Tree.branch (98 : Fin 175) _ = Tree.branch (98 : Fin 175) _
  apply congrArg (Tree.branch (98 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0315
  · exact treeEq0343
  · rfl
  · rfl

def B0048 : Block := .branch 89 ![1238242271318996484309909889, 309636125548797447127434754, 130601785896986981739534340, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448] ![Tip0048_0049, B0314, (.leaf 2 (Common.fact 270).pointIds 270), (.leaf 3 (Common.fact 271).pointIds 271), (.leaf 4 (Common.fact 272).pointIds 272), (.leaf 5 (Common.fact 273).pointIds 273), (.leaf 6 (Common.fact 274).pointIds 274)]
theorem treeEq0048 : B0048.tree = HexagonCover.NBand.M8500_8700.SplitData.node0048 := by
  change Tree.branch (89 : Fin 175) _ = Tree.branch (89 : Fin 175) _
  apply congrArg (Tree.branch (89 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0314
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0048 : B0048.accepted = true := by decide +kernel
theorem checked0048 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node0048 (maskNeeds ![1238242271318996484309909889, 309636125548797447127434754, 130601785896986981739534340, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq0048]
  exact B0048.sound accepted0048
#print axioms checked0048

end HexagonCover.NBand.M8500_8700.SplitTree.Run0005
