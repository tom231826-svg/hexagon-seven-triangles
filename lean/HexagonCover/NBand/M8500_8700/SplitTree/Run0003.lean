import HexagonCover.NBand.M8500_8700.SplitData
import HexagonCover.NBand.M8500_8700.SplitTree.Run0002
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8500_8700.SplitTree.Run0003
open OwnerTree HexagonCover.NBand.M8500_8700

abbrev Block := Chunk (n := 175) (Certificate := Fin 1173) (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck

def B0293 : Block := .branch 170 ![20770455703709558964926171586756993, 309485009821345618480596482, 130601767450242908029982724, 5846006549323611672814739330865132078623730196488, 324518553658426726783156020674576, 982134831577882783403023582264938259837693706240032, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 722).pointIds 722), (.leaf 1 (Common.fact 505).pointIds 505), (.leaf 2 (Common.fact 487).pointIds 487), (.leaf 3 (Common.fact 656).pointIds 656), (.leaf 4 (Common.fact 723).pointIds 723), (.leaf 5 (Common.fact 562).pointIds 562), (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq0293 : B0293.tree = HexagonCover.NBand.M8500_8700.SplitData.node0293 := by
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
  · rfl

def B0292 : Block := .branch 169 ![20770455703709558964926171586756993, 309485009821345618480596482, 130601767450242908029982724, 5846006549323611672814739330865132078623730196488, 324518553658426726783156020674576, 233845993264460489282736947914201353773856244236320, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 720).pointIds 720), (.leaf 1 (Common.fact 506).pointIds 506), (.leaf 2 (Common.fact 490).pointIds 490), (.leaf 3 (Common.fact 654).pointIds 654), (.leaf 4 (Common.fact 721).pointIds 721), B0293, (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq0292 : B0292.tree = HexagonCover.NBand.M8500_8700.SplitData.node0292 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0293
  · rfl

def B0291 : Block := .branch 87 ![20770455703709558964926171586756993, 309636125548797447127434754, 130601767450242908029982724, 5846006549323611672814739330865132078623730196488, 324518553658426726783156020674576, 233845993264460489282736947914201353773856244236320, 385836443449329647932829607236202725091092001718336] ![(.leaf 0 (Common.fact 378).pointIds 378), (.leaf 1 (Common.fact 379).pointIds 379), B0292, (.leaf 3 (Common.fact 653).pointIds 653), (.leaf 4 (Common.fact 381).pointIds 381), (.leaf 5 (Common.fact 382).pointIds 382), (.leaf 6 (Common.fact 557).pointIds 557)]
theorem treeEq0291 : B0291.tree = HexagonCover.NBand.M8500_8700.SplitData.node0291 := by
  change Tree.branch (87 : Fin 175) _ = Tree.branch (87 : Fin 175) _
  apply congrArg (Tree.branch (87 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0292
  · rfl
  · rfl
  · rfl
  · rfl

def B0290 : Block := .branch 109 ![20770455703709558964926171586756993, 309636125548797447127434754, 130601767450242908029982724, 5846006549323611672893967493379396416217274146824, 324518553658426726783156020674576, 233845993264460489282736947914201353773856244236320, 385836443449329647932829607236202725091092001718336] ![(.leaf 0 (Common.fact 290).pointIds 290), (.leaf 1 (Common.fact 291).pointIds 291), (.leaf 2 (Common.fact 292).pointIds 292), (.leaf 3 (Common.fact 293).pointIds 293), B0291, (.leaf 5 (Common.fact 294).pointIds 294), (.leaf 6 (Common.fact 719).pointIds 719)]
theorem treeEq0290 : B0290.tree = HexagonCover.NBand.M8500_8700.SplitData.node0290 := by
  change Tree.branch (109 : Fin 175) _ = Tree.branch (109 : Fin 175) _
  apply congrArg (Tree.branch (109 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0291
  · rfl
  · rfl

def B0289 : Block := .branch 171 ![20770455703709558964926171586756993, 309636125548797447127434754, 130601767450242908029982724, 5992156713056701964635187042299274644926916970176520, 324518553658426726783156020674576, 233845993264460489282736947914201353773856244236320, 385836443449329647932829607236202725091092001718336] ![(.leaf 0 (Common.fact 717).pointIds 717), (.leaf 1 (Common.fact 504).pointIds 504), (.leaf 2 (Common.fact 478).pointIds 478), (.leaf 3 (Common.fact 651).pointIds 651), (.leaf 4 (Common.fact 718).pointIds 718), (.leaf 5 (Common.fact 555).pointIds 555), B0290]
theorem treeEq0289 : B0289.tree = HexagonCover.NBand.M8500_8700.SplitData.node0289 := by
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
  · exact treeEq0290

def B0288 : Block := .branch 172 ![20770455703709558964926171586756993, 309636125548797447127434754, 130601767450242908029982724, 5846006549323611672893967493379396416217274146824, 324518553658426726783156020674576, 233845993264460489282736947914201353773856244236320, 385836443449329647932829607236202725091092001718336] ![(.leaf 0 (Common.fact 715).pointIds 715), (.leaf 1 (Common.fact 502).pointIds 502), (.leaf 2 (Common.fact 480).pointIds 480), B0289, (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 552).pointIds 552), (.leaf 6 (Common.fact 471).pointIds 471)]
theorem treeEq0288 : B0288.tree = HexagonCover.NBand.M8500_8700.SplitData.node0288 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0289
  · rfl
  · rfl
  · rfl

def B0287 : Block := .branch 168 ![20770455703709558964926171586756993, 309636125548797447127434754, 130601767450242908029982724, 5846006549323611672893967493379396416217274146824, 324518553658426726783156020674576, 233845993264460489282736947914201353773856244236320, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 713).pointIds 713), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 477).pointIds 477), (.leaf 3 (Common.fact 648).pointIds 648), (.leaf 4 (Common.fact 714).pointIds 714), (.leaf 5 (Common.fact 550).pointIds 550), B0288]
theorem treeEq0287 : B0287.tree = HexagonCover.NBand.M8500_8700.SplitData.node0287 := by
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
  · exact treeEq0288

def B0286 : Block := .branch 162 ![20770455703709558964926171586756993, 309636125548797447127434754, 130601767450242908029982724, 79228162514264337593543974920, 324518553658426726783156020674576, 233845993264460489282736947914201353773856244236320, 11692024325285608097096382553318234372623019016256] ![(.leaf 0 (Common.fact 373).pointIds 373), (.leaf 1 (Common.fact 374).pointIds 374), (.leaf 2 (Common.fact 375).pointIds 375), B0287, (.leaf 4 (Common.fact 712).pointIds 712), (.leaf 5 (Common.fact 376).pointIds 376), (.leaf 6 (Common.fact 377).pointIds 377)]
theorem treeEq0286 : B0286.tree = HexagonCover.NBand.M8500_8700.SplitData.node0286 := by
  change Tree.branch (162 : Fin 175) _ = Tree.branch (162 : Fin 175) _
  apply congrArg (Tree.branch (162 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0287
  · rfl
  · rfl
  · rfl

def B0285 : Block := .branch 114 ![1268269570248450804186269876609, 309636125548797447127434754, 130601767450242908029982724, 79228162514264337593543974920, 324518553658426726783156020674576, 233845993264460489282736947914201353773856244236320, 11692024325285608097096382553318234372623019016256] ![B0286, (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 308).pointIds 308), (.leaf 5 (Common.fact 309).pointIds 309), (.leaf 6 (Common.fact 658).pointIds 658)]
theorem treeEq0285 : B0285.tree = HexagonCover.NBand.M8500_8700.SplitData.node0285 := by
  change Tree.branch (114 : Fin 175) _ = Tree.branch (114 : Fin 175) _
  apply congrArg (Tree.branch (114 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0286
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0284 : Block := .branch 144 ![1268269570248450804186269876609, 309636125548797447127434754, 130601767450242908029982724, 79228162514264337593543974920, 324518553658426726783156020674576, 233845970963715290752113806378483081125494738255904, 11692024325285608097096382553318234372623019016256] ![(.leaf 0 (Common.fact 340).pointIds 340), (.leaf 1 (Common.fact 341).pointIds 341), (.leaf 2 (Common.fact 342).pointIds 342), (.leaf 3 (Common.fact 343).pointIds 343), (.leaf 4 (Common.fact 344).pointIds 344), B0285, (.leaf 6 (Common.fact 590).pointIds 590)]
theorem treeEq0284 : B0284.tree = HexagonCover.NBand.M8500_8700.SplitData.node0284 := by
  change Tree.branch (144 : Fin 175) _ = Tree.branch (144 : Fin 175) _
  apply congrArg (Tree.branch (144 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0285
  · rfl

def B0283 : Block := .branch 166 ![1268269570248450804186269876609, 309636125548797447127434754, 130601767450242908029982724, 79228162514264337593543974920, 324518553658426726783156020674576, 233845970963715290752113806378483081125494738255904, 11692024325285608097096382553318234372623019016256] ![B0284, (.leaf 1 (Common.fact 694).pointIds 694), (.leaf 2 (Common.fact 695).pointIds 695), (.leaf 3 (Common.fact 696).pointIds 696), (.leaf 4 (Common.fact 697).pointIds 697), (.leaf 5 (Common.fact 710).pointIds 710), (.leaf 6 (Common.fact 711).pointIds 711)]
theorem treeEq0283 : B0283.tree = HexagonCover.NBand.M8500_8700.SplitData.node0283 := by
  change Tree.branch (166 : Fin 175) _ = Tree.branch (166 : Fin 175) _
  apply congrArg (Tree.branch (166 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0284
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0282 : Block := .branch 152 ![1268269570248450804186269876609, 309636125548797447127434754, 130601767450242908029982724, 79228162514264337593543974920, 1393796575232682500004409118823678614798352, 233840261972944466912589573234605283144949207269408, 11692024325285608097096382553318234372623019016256] ![(.leaf 0 (Common.fact 354).pointIds 354), (.leaf 1 (Common.fact 355).pointIds 355), (.leaf 2 (Common.fact 356).pointIds 356), (.leaf 3 (Common.fact 357).pointIds 357), (.leaf 4 (Common.fact 358).pointIds 358), B0283, (.leaf 6 (Common.fact 546).pointIds 546)]
theorem treeEq0282 : B0282.tree = HexagonCover.NBand.M8500_8700.SplitData.node0282 := by
  change Tree.branch (152 : Fin 175) _ = Tree.branch (152 : Fin 175) _
  apply congrArg (Tree.branch (152 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0283
  · rfl

def B0281 : Block := .branch 163 ![1268269570248450804186269876609, 309636125548797447127434754, 130601767450242908029982724, 79228162514264337593543974920, 1393796575232682500004409118823678614798352, 233840261972944466912589573234605283144949207269408, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 709).pointIds 709), (.leaf 5 (Common.fact 387).pointIds 387), B0282]
theorem treeEq0281 : B0281.tree = HexagonCover.NBand.M8500_8700.SplitData.node0281 := by
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
  · exact treeEq0282

def B0280 : Block := .branch 165 ![1268269570248450804186269876609, 309636125548797447127434754, 130601767450242908029982724, 79228162514264337593543974920, 1393796575232682500004409118823678614798352, 187072209578355573530071658587684226515959365894176, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 708).pointIds 708), B0281, (.leaf 0 [] 0)]
theorem treeEq0280 : B0280.tree = HexagonCover.NBand.M8500_8700.SplitData.node0280 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0281
  · rfl

def B0279 : Block := .branch 167 ![1268269570248450804186269876609, 309636125548797447127434754, 130601767450242908029982724, 79228162514264337593543974920, 1393796575232682500004409118823678614798352, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 707).pointIds 707), B0280, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq0279 : B0279.tree = HexagonCover.NBand.M8500_8700.SplitData.node0279 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0280
  · rfl

theorem accepted0279 : B0279.accepted = true := by decide +kernel
theorem checked0279 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node0279 (maskNeeds ![1268269570248450804186269876609, 309636125548797447127434754, 130601767450242908029982724, 79228162514264337593543974920, 1393796575232682500004409118823678614798352, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq0279]
  exact B0279.sound accepted0279
#print axioms checked0279

def Tip0050_0055 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node0055 ![15576891194574503106994178554331521, 309636125548797447127434754, 130601767450242908029982724, 316912650057057350374175825928, 1393796575557201053662835845606834635374608, 393248, 11226638384751466903891587970215375558672448] HexagonCover.NBand.M8500_8700.SplitTree.Run0002.checked0055
def Tip0050_0219 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node0219 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 324835466308483784133530196402184, 1393796575557201053662835845606834635374608, 393248, 11226638389943763762426415598745871887892544] HexagonCover.NBand.M8500_8700.SplitTree.Run0002.checked0219
def Tip0050_0279 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node0279 ![1268269570248450804186269876609, 309636125548797447127434754, 130601767450242908029982724, 79228162514264337593543974920, 1393796575232682500004409118823678614798352, 393248, 11226638384751466903891587970215375558672448] checked0279
def B0218 : Block := .branch 169 ![5192297477504847849933185895891329, 309485009821345618480596482, 130601767450242908029982724, 324835466308483784133530196402184, 649037107316853453566312041250832, 1496577676626844588240573268701473812127674924400672, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 674).pointIds 674), (.leaf 1 (Common.fact 506).pointIds 506), (.leaf 2 (Common.fact 490).pointIds 490), (.leaf 3 (Common.fact 675).pointIds 675), (.leaf 4 (Common.fact 639).pointIds 639), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq0218 : B0218.tree = HexagonCover.NBand.M8500_8700.SplitData.node0218 := by
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

def B0217 : Block := .branch 170 ![5192297477504847849933185895891329, 309485009821345618480596482, 130601767450242908029982724, 324835466308483784133530196402184, 649037107316853453566312041250832, 393248, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 671).pointIds 671), (.leaf 1 (Common.fact 505).pointIds 505), (.leaf 2 (Common.fact 487).pointIds 487), (.leaf 3 (Common.fact 672).pointIds 672), (.leaf 4 (Common.fact 642).pointIds 642), B0218, (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq0217 : B0217.tree = HexagonCover.NBand.M8500_8700.SplitData.node0217 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0218
  · rfl

def B0216 : Block := .branch 171 ![5192297477504847849933185895891329, 309485009821345618480596482, 130601767450242908029982724, 5986310706507378353287128541114379032644229892431880, 649037107316853453566312041250832, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 669).pointIds 669), (.leaf 1 (Common.fact 504).pointIds 504), (.leaf 2 (Common.fact 478).pointIds 478), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 637).pointIds 637), (.leaf 5 (Common.fact 566).pointIds 566), B0217]
theorem treeEq0216 : B0216.tree = HexagonCover.NBand.M8500_8700.SplitData.node0216 := by
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
  · exact treeEq0217

def B0215 : Block := .branch 172 ![5192297477504847849933185895891329, 309485009821345618480596482, 130601767450242908029982724, 324835466308483784133530196402184, 649037107316853453566312041250832, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 667).pointIds 667), (.leaf 1 (Common.fact 502).pointIds 502), (.leaf 2 (Common.fact 480).pointIds 480), B0216, (.leaf 4 (Common.fact 634).pointIds 634), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq0215 : B0215.tree = HexagonCover.NBand.M8500_8700.SplitData.node0215 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0216
  · rfl
  · rfl
  · rfl

def B0054 : Block := .branch 113 ![5192297477504847849933185895891329, 309636125548797447127434754, 130601767450242908029982724, 324835466308483784133530196402184, 1393796575557201053662835845606834635374608, 393248, 11226638384751466903891587970215375558672448] ![Tip0050_0055, (.leaf 1 (Common.fact 300).pointIds 300), (.leaf 2 (Common.fact 301).pointIds 301), (.leaf 3 (Common.fact 302).pointIds 302), (.leaf 4 (Common.fact 303).pointIds 303), (.leaf 5 (Common.fact 304).pointIds 304), B0215]
theorem treeEq0054 : B0054.tree = HexagonCover.NBand.M8500_8700.SplitData.node0054 := by
  change Tree.branch (113 : Fin 175) _ = Tree.branch (113 : Fin 175) _
  apply congrArg (Tree.branch (113 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0215

def B0053 : Block := .branch 112 ![1268269570248450804186269876609, 309636125548797447127434754, 130601767450242908029982724, 324835466308483784133530196402184, 1393796575557201053662835845606834635374608, 393248, 11226638384751466903891587970215375558672448] ![B0054, (.leaf 1 (Common.fact 295).pointIds 295), (.leaf 2 (Common.fact 296).pointIds 296), (.leaf 3 (Common.fact 297).pointIds 297), (.leaf 4 (Common.fact 298).pointIds 298), (.leaf 5 (Common.fact 299).pointIds 299), Tip0050_0219]
theorem treeEq0053 : B0053.tree = HexagonCover.NBand.M8500_8700.SplitData.node0053 := by
  change Tree.branch (112 : Fin 175) _ = Tree.branch (112 : Fin 175) _
  apply congrArg (Tree.branch (112 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0054
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0278 : Block := .branch 168 ![31155049420779214221987164245197185, 309485009821345618480596482, 130601767450242908029982724, 324835466308483784133530196402184, 2854495386741147757901487811802797333045936144, 5731291516022370147374679596070628907037360160, 11193971278176093918715957461468237851525184] ![(.leaf 0 (Common.fact 704).pointIds 704), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 477).pointIds 477), (.leaf 3 (Common.fact 678).pointIds 678), (.leaf 4 (Common.fact 705).pointIds 705), (.leaf 5 (Common.fact 405).pointIds 405), (.leaf 6 (Common.fact 706).pointIds 706)]
theorem treeEq0278 : B0278.tree = HexagonCover.NBand.M8500_8700.SplitData.node0278 := by
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

def B0277 : Block := .branch 113 ![20770455703709558964926171586756993, 309485009821345618480596482, 130601767450242908029982724, 324835466308483784133530196402184, 2854495386741147757901487811802797333045936144, 5731291516022370147374679596070628907037360160, 11193971278176093918715957461468237851525184] ![B0278, (.leaf 1 (Common.fact 300).pointIds 300), (.leaf 2 (Common.fact 301).pointIds 301), (.leaf 3 (Common.fact 302).pointIds 302), (.leaf 4 (Common.fact 303).pointIds 303), (.leaf 5 (Common.fact 304).pointIds 304), (.leaf 6 (Common.fact 703).pointIds 703)]
theorem treeEq0277 : B0277.tree = HexagonCover.NBand.M8500_8700.SplitData.node0277 := by
  change Tree.branch (113 : Fin 175) _ = Tree.branch (113 : Fin 175) _
  apply congrArg (Tree.branch (113 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0278
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0276 : Block := .branch 114 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 324835466308483784133530196402184, 2854495386741147757901487811802797333045936144, 5731291516022370147374679596070628907037360160, 11193971278176093918715957461468237851525184] ![B0277, (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 308).pointIds 308), (.leaf 5 (Common.fact 309).pointIds 309), (.leaf 6 (Common.fact 702).pointIds 702)]
theorem treeEq0276 : B0276.tree = HexagonCover.NBand.M8500_8700.SplitData.node0276 := by
  change Tree.branch (114 : Fin 175) _ = Tree.branch (114 : Fin 175) _
  apply congrArg (Tree.branch (114 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0277
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0275 : Block := .branch 144 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 324835466308483784133530196402184, 2854495386741147757901487811802797333045936144, 5708990770823839524233143877797980545531379744, 11193971278176093918715957461468237851525184] ![(.leaf 0 (Common.fact 340).pointIds 340), (.leaf 1 (Common.fact 341).pointIds 341), (.leaf 2 (Common.fact 342).pointIds 342), (.leaf 3 (Common.fact 343).pointIds 343), (.leaf 4 (Common.fact 344).pointIds 344), B0276, (.leaf 6 (Common.fact 701).pointIds 701)]
theorem treeEq0275 : B0275.tree = HexagonCover.NBand.M8500_8700.SplitData.node0275 := by
  change Tree.branch (144 : Fin 175) _ = Tree.branch (144 : Fin 175) _
  apply congrArg (Tree.branch (144 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0276
  · rfl

def B0274 : Block := .branch 151 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 324835466308483784133530196402184, 1329227995784915872903807060280442896, 5708990770823839524233143877797980545531379744, 11193971278176093918715957461468237851525184] ![(.leaf 0 (Common.fact 349).pointIds 349), (.leaf 1 (Common.fact 350).pointIds 350), (.leaf 2 (Common.fact 351).pointIds 351), (.leaf 3 (Common.fact 352).pointIds 352), B0275, (.leaf 5 (Common.fact 353).pointIds 353), (.leaf 6 (Common.fact 700).pointIds 700)]
theorem treeEq0274 : B0274.tree = HexagonCover.NBand.M8500_8700.SplitData.node0274 := by
  change Tree.branch (151 : Fin 175) _ = Tree.branch (151 : Fin 175) _
  apply congrArg (Tree.branch (151 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0275
  · rfl
  · rfl

def B0273 : Block := .branch 166 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 324835466308483784133530196402184, 1329227995784915872903807060280442896, 5708990770823839524233143877797980545531379744, 11193971278176093918715957461468237851525184] ![B0274, (.leaf 1 (Common.fact 694).pointIds 694), (.leaf 2 (Common.fact 695).pointIds 695), (.leaf 3 (Common.fact 696).pointIds 696), (.leaf 4 (Common.fact 697).pointIds 697), (.leaf 5 (Common.fact 698).pointIds 698), (.leaf 6 (Common.fact 699).pointIds 699)]
theorem treeEq0273 : B0273.tree = HexagonCover.NBand.M8500_8700.SplitData.node0273 := by
  change Tree.branch (166 : Fin 175) _ = Tree.branch (166 : Fin 175) _
  apply congrArg (Tree.branch (166 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0274
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0272 : Block := .branch 152 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 324835466308483784133530196402184, 1393797904136159731261855295847582874566672, 393248, 11193971278176093918715957461468237851525184] ![(.leaf 0 (Common.fact 354).pointIds 354), (.leaf 1 (Common.fact 355).pointIds 355), (.leaf 2 (Common.fact 356).pointIds 356), (.leaf 3 (Common.fact 357).pointIds 357), (.leaf 4 (Common.fact 358).pointIds 358), B0273, (.leaf 6 (Common.fact 693).pointIds 693)]
theorem treeEq0272 : B0272.tree = HexagonCover.NBand.M8500_8700.SplitData.node0272 := by
  change Tree.branch (152 : Fin 175) _ = Tree.branch (152 : Fin 175) _
  apply congrArg (Tree.branch (152 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0273
  · rfl

def B0052 : Block := .branch 109 ![1268269570248450804186269876609, 309636125548797447127434754, 130601767450242908029982724, 324914694470998048471123740352520, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 290).pointIds 290), (.leaf 1 (Common.fact 291).pointIds 291), (.leaf 2 (Common.fact 292).pointIds 292), (.leaf 3 (Common.fact 293).pointIds 293), B0053, (.leaf 5 (Common.fact 294).pointIds 294), B0272]
theorem treeEq0052 : B0052.tree = HexagonCover.NBand.M8500_8700.SplitData.node0052 := by
  change Tree.branch (109 : Fin 175) _ = Tree.branch (109 : Fin 175) _
  apply congrArg (Tree.branch (109 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0053
  · rfl
  · exact treeEq0272

def B0051 : Block := .branch 108 ![1268269570248450804186269876609, 309636125548797447127434754, 130601767450242908029982724, 396140812571321687967719776264, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), B0052, Tip0050_0279, (.leaf 5 (Common.fact 288).pointIds 288), (.leaf 6 (Common.fact 289).pointIds 289)]
theorem treeEq0051 : B0051.tree = HexagonCover.NBand.M8500_8700.SplitData.node0051 := by
  change Tree.branch (108 : Fin 175) _ = Tree.branch (108 : Fin 175) _
  apply congrArg (Tree.branch (108 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0052
  · rfl
  · rfl
  · rfl

def B0297 : Block := .branch 172 ![618970020221402689566671233, 309485009821345618480596482, 130601767450242908029982724, 2993155353254369741214988414329874373470213384462344, 11692013098647223345629478661730264157247460442128, 393248, 11193971277528324461999332237303422513578048] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 502).pointIds 502), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 664).pointIds 664), (.leaf 4 (Common.fact 665).pointIds 665), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 728).pointIds 728)]
theorem treeEq0297 : B0297.tree = HexagonCover.NBand.M8500_8700.SplitData.node0297 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0296 : Block := .branch 171 ![618970020221402689566671233, 309485009821345618480596482, 130601767450242908029982724, 680564733841876926926749214863536447496, 11692013098647223345629478661730264157247460442128, 393248, 11193971277528324461999332237303422513578048] ![(.leaf 0 (Common.fact 725).pointIds 725), (.leaf 1 (Common.fact 504).pointIds 504), (.leaf 2 (Common.fact 478).pointIds 478), B0297, (.leaf 4 (Common.fact 661).pointIds 661), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 726).pointIds 726)]
theorem treeEq0296 : B0296.tree = HexagonCover.NBand.M8500_8700.SplitData.node0296 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0297
  · rfl
  · rfl
  · rfl

def B0295 : Block := .branch 129 ![618970020221402689566671233, 309485009821345618480596482, 130601767450242908029982724, 24584, 11692013098647223345629478661730264157247460442128, 393248, 11226638384752734554491816199616872261877824] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), (.leaf 2 (Common.fact 322).pointIds 322), B0296, (.leaf 4 (Common.fact 659).pointIds 659), (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 6 (Common.fact 324).pointIds 324)]
theorem treeEq0295 : B0295.tree = HexagonCover.NBand.M8500_8700.SplitData.node0295 := by
  change Tree.branch (129 : Fin 175) _ = Tree.branch (129 : Fin 175) _
  apply congrArg (Tree.branch (129 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0296
  · rfl
  · rfl
  · rfl

def B0294 : Block := .branch 163 ![618970020221402689566671233, 309485009821345618480596482, 130601767450242908029982724, 24584, 98320, 393248, 11226638384752734554491816199616872261877824] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), B0295, (.leaf 5 (Common.fact 387).pointIds 387), (.leaf 6 (Common.fact 724).pointIds 724)]
theorem treeEq0294 : B0294.tree = HexagonCover.NBand.M8500_8700.SplitData.node0294 := by
  change Tree.branch (163 : Fin 175) _ = Tree.branch (163 : Fin 175) _
  apply congrArg (Tree.branch (163 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0295
  · rfl
  · rfl

def B0050 : Block := .branch 100 ![618970020221402689566671233, 309636125548797447127434754, 130601767450242908029982724, 396140812571321687967719776264, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448] ![B0051, (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 281).pointIds 281), (.leaf 3 (Common.fact 282).pointIds 282), (.leaf 4 (Common.fact 283).pointIds 283), (.leaf 5 (Common.fact 284).pointIds 284), B0294]
theorem treeEq0050 : B0050.tree = HexagonCover.NBand.M8500_8700.SplitData.node0050 := by
  change Tree.branch (100 : Fin 175) _ = Tree.branch (100 : Fin 175) _
  apply congrArg (Tree.branch (100 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0051
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0294

theorem accepted0050 : B0050.accepted = true := by decide +kernel
theorem checked0050 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node0050 (maskNeeds ![618970020221402689566671233, 309636125548797447127434754, 130601767450242908029982724, 396140812571321687967719776264, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq0050]
  exact B0050.sound accepted0050
#print axioms checked0050

def B0323 : Block := .branch 169 ![1238242271318996484309909889, 928455029464035755930158594, 130601767450242908029982724, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993886115266325905467305191218409773667103624659008] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 752).pointIds 752), (.leaf 2 (Common.fact 490).pointIds 490), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq0323 : B0323.tree = HexagonCover.NBand.M8500_8700.SplitData.node0323 := by
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

def B0322 : Block := .branch 170 ![1238242271318996484309909889, 928455029464035755930158594, 130601767450242908029982724, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993886115266325905467305191218409773667103624659008] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 747).pointIds 747), (.leaf 2 (Common.fact 487).pointIds 487), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B0323, (.leaf 6 (Common.fact 750).pointIds 750)]
theorem treeEq0322 : B0322.tree = HexagonCover.NBand.M8500_8700.SplitData.node0322 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0323
  · rfl

def B0321 : Block := .branch 171 ![1238242271318996484309909889, 928455029464035755930158594, 130601767450242908029982724, 5986310706507378353287286997439407561319416980332552, 1329227995784915872903807060280442896, 393248, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 743).pointIds 743), (.leaf 1 (Common.fact 744).pointIds 744), (.leaf 2 (Common.fact 478).pointIds 478), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B0322]
theorem treeEq0321 : B0321.tree = HexagonCover.NBand.M8500_8700.SplitData.node0321 := by
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
  · exact treeEq0322

def B0320 : Block := .branch 172 ![1238242271318996484309909889, 928455029464035755930158594, 130601767450242908029982724, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 740).pointIds 740), (.leaf 1 (Common.fact 741).pointIds 741), (.leaf 2 (Common.fact 480).pointIds 480), B0321, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 503).pointIds 503)]
theorem treeEq0320 : B0320.tree = HexagonCover.NBand.M8500_8700.SplitData.node0320 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0321
  · rfl
  · rfl
  · rfl

def B0319 : Block := .branch 159 ![5193565747377327176928477342335361, 928455029464035755930158594, 130601767450242908029982724, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 738).pointIds 738), (.leaf 1 (Common.fact 739).pointIds 739), (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), B0320]
theorem treeEq0319 : B0319.tree = HexagonCover.NBand.M8500_8700.SplitData.node0319 := by
  change Tree.branch (159 : Fin 175) _ = Tree.branch (159 : Fin 175) _
  apply congrArg (Tree.branch (159 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0320

def B0329 : Block := .branch 169 ![1238242271318996484309909889, 928455029464035755930158594, 130601767450242908029982724, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993886115266325910659602049753237402197599953879104] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 752).pointIds 752), (.leaf 2 (Common.fact 490).pointIds 490), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 759).pointIds 759)]
theorem treeEq0329 : B0329.tree = HexagonCover.NBand.M8500_8700.SplitData.node0329 := by
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

def B0328 : Block := .branch 170 ![1238242271318996484309909889, 928455029464035755930158594, 130601767450242908029982724, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993886115266325910659602049753237402197599953879104] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 747).pointIds 747), (.leaf 2 (Common.fact 487).pointIds 487), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B0329, (.leaf 6 (Common.fact 758).pointIds 758)]
theorem treeEq0328 : B0328.tree = HexagonCover.NBand.M8500_8700.SplitData.node0328 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0329
  · rfl

def B0327 : Block := .branch 171 ![1238242271318996484309909889, 928455029464035755930158594, 130601767450242908029982724, 5986310706507378353287286997439407561319416980332552, 1329227995784915872903807060280442896, 393248, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 743).pointIds 743), (.leaf 1 (Common.fact 744).pointIds 744), (.leaf 2 (Common.fact 478).pointIds 478), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B0328]
theorem treeEq0327 : B0327.tree = HexagonCover.NBand.M8500_8700.SplitData.node0327 := by
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
  · exact treeEq0328

def B0326 : Block := .branch 172 ![1238242271318996484309909889, 928455029464035755930158594, 130601767450242908029982724, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 740).pointIds 740), (.leaf 1 (Common.fact 741).pointIds 741), (.leaf 2 (Common.fact 480).pointIds 480), B0327, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq0326 : B0326.tree = HexagonCover.NBand.M8500_8700.SplitData.node0326 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0327
  · rfl
  · rfl
  · rfl

def B0325 : Block := .branch 159 ![10385862605912154805458973671555457, 928455029464035755930158594, 130601767450242908029982724, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 756).pointIds 756), (.leaf 1 (Common.fact 739).pointIds 739), (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), B0326]
theorem treeEq0325 : B0325.tree = HexagonCover.NBand.M8500_8700.SplitData.node0325 := by
  change Tree.branch (159 : Fin 175) _ = Tree.branch (159 : Fin 175) _
  apply congrArg (Tree.branch (159 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0326

def B0333 : Block := .branch 169 ![1238242271318996484309909889, 928455029464035755930158594, 130601767450242908029982724, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 752).pointIds 752), (.leaf 2 (Common.fact 490).pointIds 490), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq0333 : B0333.tree = HexagonCover.NBand.M8500_8700.SplitData.node0333 := by
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

def B0332 : Block := .branch 170 ![1238242271318996484309909889, 928455029464035755930158594, 130601767450242908029982724, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 747).pointIds 747), (.leaf 2 (Common.fact 487).pointIds 487), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B0333, (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq0332 : B0332.tree = HexagonCover.NBand.M8500_8700.SplitData.node0332 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0333
  · rfl

def B0331 : Block := .branch 171 ![1238242271318996484309909889, 928455029464035755930158594, 130601767450242908029982724, 5986310706507378353287286997439407561319416980332552, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 743).pointIds 743), (.leaf 1 (Common.fact 744).pointIds 744), (.leaf 2 (Common.fact 478).pointIds 478), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B0332]
theorem treeEq0331 : B0331.tree = HexagonCover.NBand.M8500_8700.SplitData.node0331 := by
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
  · exact treeEq0332

def B0330 : Block := .branch 172 ![1238242271318996484309909889, 928455029464035755930158594, 130601767450242908029982724, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 740).pointIds 740), (.leaf 1 (Common.fact 741).pointIds 741), (.leaf 2 (Common.fact 480).pointIds 480), B0331, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq0330 : B0330.tree = HexagonCover.NBand.M8500_8700.SplitData.node0330 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0331
  · rfl
  · rfl
  · rfl

def B0324 : Block := .branch 113 ![1268888842499548397981013115265, 928455029464035755930158594, 130601767450242908029982724, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971282719353669933931636432422139592768] ![B0325, (.leaf 1 (Common.fact 300).pointIds 300), (.leaf 2 (Common.fact 301).pointIds 301), (.leaf 3 (Common.fact 302).pointIds 302), (.leaf 4 (Common.fact 303).pointIds 303), (.leaf 5 (Common.fact 304).pointIds 304), B0330]
theorem treeEq0324 : B0324.tree = HexagonCover.NBand.M8500_8700.SplitData.node0324 := by
  change Tree.branch (113 : Fin 175) _ = Tree.branch (113 : Fin 175) _
  apply congrArg (Tree.branch (113 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0325
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0330

def B0318 : Block := .branch 112 ![1268888842499548397981013115265, 928455029464035755930158594, 130601767450242908029982724, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![B0319, (.leaf 1 (Common.fact 295).pointIds 295), (.leaf 2 (Common.fact 296).pointIds 296), (.leaf 3 (Common.fact 297).pointIds 297), (.leaf 4 (Common.fact 298).pointIds 298), (.leaf 5 (Common.fact 299).pointIds 299), B0324]
theorem treeEq0318 : B0318.tree = HexagonCover.NBand.M8500_8700.SplitData.node0318 := by
  change Tree.branch (112 : Fin 175) _ = Tree.branch (112 : Fin 175) _
  apply congrArg (Tree.branch (112 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0319
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0324

def B0335 : Block := .branch 168 ![1238242271318996484309909889, 928455029464035755930158594, 130601767450242908029982724, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 11193971278176093918715957461468237851525184] ![(.leaf 0 (Common.fact 761).pointIds 761), (.leaf 1 (Common.fact 762).pointIds 762), (.leaf 2 (Common.fact 477).pointIds 477), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 765).pointIds 765), (.leaf 6 (Common.fact 706).pointIds 706)]
theorem treeEq0335 : B0335.tree = HexagonCover.NBand.M8500_8700.SplitData.node0335 := by
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

def B0334 : Block := .branch 170 ![1238242271318996484309909889, 928455029464035755930158594, 130601767450242908029982724, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 11193971278176093918715957461468237851525184] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 747).pointIds 747), (.leaf 2 (Common.fact 487).pointIds 487), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B0335, (.leaf 6 (Common.fact 760).pointIds 760)]
theorem treeEq0334 : B0334.tree = HexagonCover.NBand.M8500_8700.SplitData.node0334 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0335
  · rfl

def B0317 : Block := .branch 109 ![1268888842499548397981013115265, 928455029464035755930158594, 130601767450242908029982724, 325073150796026577146310828253192, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 290).pointIds 290), (.leaf 1 (Common.fact 291).pointIds 291), (.leaf 2 (Common.fact 292).pointIds 292), (.leaf 3 (Common.fact 293).pointIds 293), B0318, (.leaf 5 (Common.fact 294).pointIds 294), B0334]
theorem treeEq0317 : B0317.tree = HexagonCover.NBand.M8500_8700.SplitData.node0317 := by
  change Tree.branch (109 : Fin 175) _ = Tree.branch (109 : Fin 175) _
  apply congrArg (Tree.branch (109 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0318
  · rfl
  · exact treeEq0334

theorem accepted0317 : B0317.accepted = true := by decide +kernel
theorem checked0317 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node0317 (maskNeeds ![1268888842499548397981013115265, 928455029464035755930158594, 130601767450242908029982724, 325073150796026577146310828253192, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672]) := by
  rw [← treeEq0317]
  exact B0317.sound accepted0317
#print axioms checked0317

def Tip0049_0050 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node0050 ![618970020221402689566671233, 309636125548797447127434754, 130601767450242908029982724, 396140812571321687967719776264, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448] checked0050
def B0313 : Block := .branch 170 ![20770455703709558964926171586756993, 309485009821345618480596482, 130601767450242908029982724, 5846006549323611672814739330865132078623730196488, 316912650057057350374175899664, 982134831577882783403023582264938259837693706240032, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 722).pointIds 722), (.leaf 1 (Common.fact 505).pointIds 505), (.leaf 2 (Common.fact 487).pointIds 487), (.leaf 3 (Common.fact 656).pointIds 656), (.leaf 4 (Common.fact 737).pointIds 737), (.leaf 5 (Common.fact 562).pointIds 562), (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq0313 : B0313.tree = HexagonCover.NBand.M8500_8700.SplitData.node0313 := by
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
  · rfl

def B0312 : Block := .branch 169 ![20770455703709558964926171586756993, 309485009821345618480596482, 130601767450242908029982724, 5846006549323611672814739330865132078623730196488, 316912650057057350374175899664, 233845993264460489282736947914201353773856244236320, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 720).pointIds 720), (.leaf 1 (Common.fact 506).pointIds 506), (.leaf 2 (Common.fact 490).pointIds 490), (.leaf 3 (Common.fact 654).pointIds 654), (.leaf 4 (Common.fact 736).pointIds 736), B0313, (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq0312 : B0312.tree = HexagonCover.NBand.M8500_8700.SplitData.node0312 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0313
  · rfl

def B0311 : Block := .branch 87 ![20770455703709558964926171586756993, 309636125548797447127434754, 130601767450242908029982724, 5846006549323611672814739330865132078623730196488, 316912650057057350374175899664, 233845993264460489282736947914201353773856244236320, 385836443449329647932829607236202725091092001718336] ![(.leaf 0 (Common.fact 378).pointIds 378), (.leaf 1 (Common.fact 379).pointIds 379), B0312, (.leaf 3 (Common.fact 653).pointIds 653), (.leaf 4 (Common.fact 381).pointIds 381), (.leaf 5 (Common.fact 382).pointIds 382), (.leaf 6 (Common.fact 557).pointIds 557)]
theorem treeEq0311 : B0311.tree = HexagonCover.NBand.M8500_8700.SplitData.node0311 := by
  change Tree.branch (87 : Fin 175) _ = Tree.branch (87 : Fin 175) _
  apply congrArg (Tree.branch (87 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0312
  · rfl
  · rfl
  · rfl
  · rfl

def B0310 : Block := .branch 109 ![20770455703709558964926171586756993, 309636125548797447127434754, 130601767450242908029982724, 5846006549323611672893967493379396416217274146824, 316912650057057350374175899664, 233845993264460489282736947914201353773856244236320, 385836443449329647932829607236202725091092001718336] ![(.leaf 0 (Common.fact 290).pointIds 290), (.leaf 1 (Common.fact 291).pointIds 291), (.leaf 2 (Common.fact 292).pointIds 292), (.leaf 3 (Common.fact 293).pointIds 293), B0311, (.leaf 5 (Common.fact 294).pointIds 294), (.leaf 6 (Common.fact 719).pointIds 719)]
theorem treeEq0310 : B0310.tree = HexagonCover.NBand.M8500_8700.SplitData.node0310 := by
  change Tree.branch (109 : Fin 175) _ = Tree.branch (109 : Fin 175) _
  apply congrArg (Tree.branch (109 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0311
  · rfl
  · rfl

def B0309 : Block := .branch 171 ![20770455703709558964926171586756993, 309636125548797447127434754, 130601767450242908029982724, 5992156713056701964635187042299274644926916970176520, 316912650057057350374175899664, 233845993264460489282736947914201353773856244236320, 385836443449329647932829607236202725091092001718336] ![(.leaf 0 (Common.fact 717).pointIds 717), (.leaf 1 (Common.fact 504).pointIds 504), (.leaf 2 (Common.fact 478).pointIds 478), (.leaf 3 (Common.fact 651).pointIds 651), (.leaf 4 (Common.fact 735).pointIds 735), (.leaf 5 (Common.fact 555).pointIds 555), B0310]
theorem treeEq0309 : B0309.tree = HexagonCover.NBand.M8500_8700.SplitData.node0309 := by
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
  · exact treeEq0310

def B0308 : Block := .branch 172 ![20770455703709558964926171586756993, 309636125548797447127434754, 130601767450242908029982724, 5846006549323611672893967493379396416217274146824, 316912650057057350374175899664, 233845993264460489282736947914201353773856244236320, 385836443449329647932829607236202725091092001718336] ![(.leaf 0 (Common.fact 715).pointIds 715), (.leaf 1 (Common.fact 502).pointIds 502), (.leaf 2 (Common.fact 480).pointIds 480), B0309, (.leaf 4 (Common.fact 734).pointIds 734), (.leaf 5 (Common.fact 552).pointIds 552), (.leaf 6 (Common.fact 471).pointIds 471)]
theorem treeEq0308 : B0308.tree = HexagonCover.NBand.M8500_8700.SplitData.node0308 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0309
  · rfl
  · rfl
  · rfl

def B0307 : Block := .branch 168 ![20770455703709558964926171586756993, 309636125548797447127434754, 130601767450242908029982724, 5846006549323611672893967493379396416217274146824, 316912650057057350374175899664, 233845993264460489282736947914201353773856244236320, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 713).pointIds 713), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 477).pointIds 477), (.leaf 3 (Common.fact 648).pointIds 648), (.leaf 4 (Common.fact 733).pointIds 733), (.leaf 5 (Common.fact 550).pointIds 550), B0308]
theorem treeEq0307 : B0307.tree = HexagonCover.NBand.M8500_8700.SplitData.node0307 := by
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
  · exact treeEq0308

def B0306 : Block := .branch 162 ![20770455703709558964926171586756993, 309636125548797447127434754, 130601767450242908029982724, 79228162514264337593543974920, 316912650057057350374175899664, 233845993264460489282736947914201353773856244236320, 11692024325285608097096382553318234372623019016256] ![(.leaf 0 (Common.fact 373).pointIds 373), (.leaf 1 (Common.fact 374).pointIds 374), (.leaf 2 (Common.fact 375).pointIds 375), B0307, (.leaf 4 (Common.fact 732).pointIds 732), (.leaf 5 (Common.fact 376).pointIds 376), (.leaf 6 (Common.fact 377).pointIds 377)]
theorem treeEq0306 : B0306.tree = HexagonCover.NBand.M8500_8700.SplitData.node0306 := by
  change Tree.branch (162 : Fin 175) _ = Tree.branch (162 : Fin 175) _
  apply congrArg (Tree.branch (162 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0307
  · rfl
  · rfl
  · rfl

def B0305 : Block := .branch 100 ![20769188053109330735524674883551617, 309636125548797447127434754, 130601767450242908029982724, 79228162514264337593543974920, 316912650057057350374175899664, 233845993264460489282736947914201353773856244236320, 11692024325285608097096382553318234372623019016256] ![B0306, (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 281).pointIds 281), (.leaf 3 (Common.fact 282).pointIds 282), (.leaf 4 (Common.fact 283).pointIds 283), (.leaf 5 (Common.fact 284).pointIds 284), (.leaf 6 (Common.fact 724).pointIds 724)]
theorem treeEq0305 : B0305.tree = HexagonCover.NBand.M8500_8700.SplitData.node0305 := by
  change Tree.branch (100 : Fin 175) _ = Tree.branch (100 : Fin 175) _
  apply congrArg (Tree.branch (100 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0306
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0304 : Block := .branch 114 ![618970020221402689566671233, 309636125548797447127434754, 130601767450242908029982724, 79228162514264337593543974920, 316912650057057350374175899664, 233845993264460489282736947914201353773856244236320, 11692024325285608097096382553318234372623019016256] ![B0305, (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 308).pointIds 308), (.leaf 5 (Common.fact 309).pointIds 309), (.leaf 6 (Common.fact 658).pointIds 658)]
theorem treeEq0304 : B0304.tree = HexagonCover.NBand.M8500_8700.SplitData.node0304 := by
  change Tree.branch (114 : Fin 175) _ = Tree.branch (114 : Fin 175) _
  apply congrArg (Tree.branch (114 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0305
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0303 : Block := .branch 144 ![618970020221402689566671233, 309636125548797447127434754, 130601767450242908029982724, 79228162514264337593543974920, 316912650057057350374175899664, 233845970963715290752113806378483081125494738255904, 11692024325285608097096382553318234372623019016256] ![(.leaf 0 (Common.fact 340).pointIds 340), (.leaf 1 (Common.fact 341).pointIds 341), (.leaf 2 (Common.fact 342).pointIds 342), (.leaf 3 (Common.fact 343).pointIds 343), (.leaf 4 (Common.fact 344).pointIds 344), B0304, (.leaf 6 (Common.fact 590).pointIds 590)]
theorem treeEq0303 : B0303.tree = HexagonCover.NBand.M8500_8700.SplitData.node0303 := by
  change Tree.branch (144 : Fin 175) _ = Tree.branch (144 : Fin 175) _
  apply congrArg (Tree.branch (144 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0304
  · rfl

def B0302 : Block := .branch 166 ![618970020221402689566671233, 309636125548797447127434754, 130601767450242908029982724, 79228162514264337593543974920, 316912650057057350374175899664, 233845970963715290752113806378483081125494738255904, 11692024325285608097096382553318234372623019016256] ![B0303, (.leaf 1 (Common.fact 694).pointIds 694), (.leaf 2 (Common.fact 695).pointIds 695), (.leaf 3 (Common.fact 696).pointIds 696), (.leaf 4 (Common.fact 697).pointIds 697), (.leaf 5 (Common.fact 710).pointIds 710), (.leaf 6 (Common.fact 711).pointIds 711)]
theorem treeEq0302 : B0302.tree = HexagonCover.NBand.M8500_8700.SplitData.node0302 := by
  change Tree.branch (166 : Fin 175) _ = Tree.branch (166 : Fin 175) _
  apply congrArg (Tree.branch (166 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0303
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0301 : Block := .branch 152 ![618970020221402689566671233, 309636125548797447127434754, 130601767450242908029982724, 79228162514264337593543974920, 1393796574908480858996039449390896770023440, 233840261972944466912589573234605283144949207269408, 11692024325285608097096382553318234372623019016256] ![(.leaf 0 (Common.fact 354).pointIds 354), (.leaf 1 (Common.fact 355).pointIds 355), (.leaf 2 (Common.fact 356).pointIds 356), (.leaf 3 (Common.fact 357).pointIds 357), (.leaf 4 (Common.fact 358).pointIds 358), B0302, (.leaf 6 (Common.fact 546).pointIds 546)]
theorem treeEq0301 : B0301.tree = HexagonCover.NBand.M8500_8700.SplitData.node0301 := by
  change Tree.branch (152 : Fin 175) _ = Tree.branch (152 : Fin 175) _
  apply congrArg (Tree.branch (152 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0302
  · rfl

def B0300 : Block := .branch 163 ![618970020221402689566671233, 309636125548797447127434754, 130601767450242908029982724, 79228162514264337593543974920, 1393796574908480858996039449390896770023440, 233840261972944466912589573234605283144949207269408, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 731).pointIds 731), (.leaf 5 (Common.fact 387).pointIds 387), B0301]
theorem treeEq0300 : B0300.tree = HexagonCover.NBand.M8500_8700.SplitData.node0300 := by
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
  · exact treeEq0301

def B0299 : Block := .branch 165 ![618970020221402689566671233, 309636125548797447127434754, 130601767450242908029982724, 79228162514264337593543974920, 1393796574908480858996039449390896770023440, 187072209578355573530071658587684226515959365894176, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 730).pointIds 730), B0300, (.leaf 0 [] 0)]
theorem treeEq0299 : B0299.tree = HexagonCover.NBand.M8500_8700.SplitData.node0299 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0300
  · rfl

def B0298 : Block := .branch 167 ![618970020221402689566671233, 309636125548797447127434754, 130601767450242908029982724, 79228162514264337593543974920, 1393796574908480858996039449390896770023440, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 729).pointIds 729), B0299, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq0298 : B0298.tree = HexagonCover.NBand.M8500_8700.SplitData.node0298 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0299
  · rfl

def B0049 : Block := .branch 98 ![618970020221402689566671233, 309636125548797447127434754, 130601785896986981739534340, 79228162514264337593543974920, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 275).pointIds 275), (.leaf 1 (Common.fact 276).pointIds 276), (.leaf 2 (Common.fact 277).pointIds 277), Tip0049_0050, B0298, (.leaf 5 (Common.fact 278).pointIds 278), (.leaf 6 (Common.fact 279).pointIds 279)]
theorem treeEq0049 : B0049.tree = HexagonCover.NBand.M8500_8700.SplitData.node0049 := by
  change Tree.branch (98 : Fin 175) _ = Tree.branch (98 : Fin 175) _
  apply congrArg (Tree.branch (98 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0298
  · rfl
  · rfl

theorem accepted0049 : B0049.accepted = true := by decide +kernel
theorem checked0049 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node0049 (maskNeeds ![618970020221402689566671233, 309636125548797447127434754, 130601785896986981739534340, 79228162514264337593543974920, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq0049]
  exact B0049.sound accepted0049
#print axioms checked0049

end HexagonCover.NBand.M8500_8700.SplitTree.Run0003
