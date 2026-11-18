import HexagonCover.NBand.M8500_8700.SplitData
import HexagonCover.NBand.M8500_8700.SplitTree.Run0000
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8500_8700.SplitTree.Run0001
open OwnerTree HexagonCover.NBand.M8500_8700

abbrev Block := Chunk (n := 175) (Certificate := Fin 1173) (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck

def Tip0063_0065 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node0065 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 89551429937849850465379425745953950848278536, 2855889181987476963170234774744597107400867856, 22300745198530623141535718272648361506373664, 11226638384751466903891587970215375558672448] HexagonCover.NBand.M8500_8700.SplitTree.Run0000.checked0065
def B0139 : Block := .branch 169 ![36346078628713813621116163871211905, 309485009821345618480596482, 130601767450242908029982724, 89551429937849850465379425745953950848278536, 5575186300281692892700783021728402417745936, 1496577676626844588240573268701473812127674924400672, 3367302626949341878426932094473566926029357430865984] ![(.leaf 0 (Common.fact 499).pointIds 499), (.leaf 1 (Common.fact 506).pointIds 506), (.leaf 2 (Common.fact 490).pointIds 490), (.leaf 3 (Common.fact 491).pointIds 491), (.leaf 4 (Common.fact 536).pointIds 536), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 537).pointIds 537)]
theorem treeEq0139 : B0139.tree = HexagonCover.NBand.M8500_8700.SplitData.node0139 := by
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

def B0138 : Block := .branch 170 ![36346078628713813621116163871211905, 309485009821345618480596482, 130601767450242908029982724, 89551429937849850465379425745953950848278536, 5575186300281692892700783021728402417745936, 393248, 3367302626949341878426932094473566926029357430865984] ![(.leaf 0 (Common.fact 497).pointIds 497), (.leaf 1 (Common.fact 505).pointIds 505), (.leaf 2 (Common.fact 487).pointIds 487), (.leaf 3 (Common.fact 488).pointIds 488), (.leaf 4 (Common.fact 534).pointIds 534), B0139, (.leaf 6 (Common.fact 535).pointIds 535)]
theorem treeEq0138 : B0138.tree = HexagonCover.NBand.M8500_8700.SplitData.node0138 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0139
  · rfl

def B0137 : Block := .branch 171 ![36346078628713813621116163871211905, 309485009821345618480596482, 130601767450242908029982724, 5986310796058808290812143540185320994464650544308232, 5575186300281692892700783021728402417745936, 5731291516022370147374679596070628907037360160, 374147273695652701945785557070619301774007582851136] ![(.leaf 0 (Common.fact 496).pointIds 496), (.leaf 1 (Common.fact 504).pointIds 504), (.leaf 2 (Common.fact 478).pointIds 478), (.leaf 3 (Common.fact 485).pointIds 485), (.leaf 4 (Common.fact 533).pointIds 533), (.leaf 5 (Common.fact 430).pointIds 430), B0138]
theorem treeEq0137 : B0137.tree = HexagonCover.NBand.M8500_8700.SplitData.node0137 := by
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
  · exact treeEq0138

def B0136 : Block := .branch 172 ![36346078628713813621116163871211905, 309485009821345618480596482, 130601767450242908029982724, 89551429937849850465379425745953950848278536, 5575186300281692892700783021728402417745936, 5731291516022370147374679596070628907037360160, 374147273695695237241650674378552223599936553877568] ![(.leaf 0 (Common.fact 494).pointIds 494), (.leaf 1 (Common.fact 502).pointIds 502), (.leaf 2 (Common.fact 480).pointIds 480), B0137, (.leaf 4 (Common.fact 531).pointIds 531), (.leaf 5 (Common.fact 432).pointIds 432), (.leaf 6 (Common.fact 532).pointIds 532)]
theorem treeEq0136 : B0136.tree = HexagonCover.NBand.M8500_8700.SplitData.node0136 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0137
  · rfl
  · rfl
  · rfl

def B0135 : Block := .branch 168 ![36346078628713813621116163871211905, 309485009821345618480596482, 130601767450242908029982724, 89551429937849850465379425745953950848278536, 5575186300281692892700783021728402417745936, 5731291516022370147374679596070628907037360160, 2854538984090181507357203183770568017822875712] ![(.leaf 0 (Common.fact 493).pointIds 493), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 477).pointIds 477), (.leaf 3 (Common.fact 482).pointIds 482), (.leaf 4 (Common.fact 530).pointIds 530), (.leaf 5 (Common.fact 405).pointIds 405), B0136]
theorem treeEq0135 : B0135.tree = HexagonCover.NBand.M8500_8700.SplitData.node0135 := by
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
  · exact treeEq0136

def B0134 : Block := .branch 152 ![36346078628713813621116163871211905, 309485009821345618480596482, 130601767450242908029982724, 89551429937849850465379425745953950848278536, 6968982875189856839046765413768925011869712, 22300745198530623141535718272648361506373664, 2854538984090181507357203183770568017822875712] ![(.leaf 0 (Common.fact 354).pointIds 354), (.leaf 1 (Common.fact 355).pointIds 355), (.leaf 2 (Common.fact 356).pointIds 356), (.leaf 3 (Common.fact 357).pointIds 357), (.leaf 4 (Common.fact 358).pointIds 358), B0135, (.leaf 6 (Common.fact 529).pointIds 529)]
theorem treeEq0134 : B0134.tree = HexagonCover.NBand.M8500_8700.SplitData.node0134 := by
  change Tree.branch (152 : Fin 175) _ = Tree.branch (152 : Fin 175) _
  apply congrArg (Tree.branch (152 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0135
  · rfl

def B0064 : Block := .branch 151 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 89551429937849850465379425745953950848278536, 6968982875189856839046765413768925011869712, 22300745198530623141535718272648361506373664, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 349).pointIds 349), (.leaf 1 (Common.fact 350).pointIds 350), (.leaf 2 (Common.fact 351).pointIds 351), (.leaf 3 (Common.fact 352).pointIds 352), Tip0063_0065, (.leaf 5 (Common.fact 353).pointIds 353), B0134]
theorem treeEq0064 : B0064.tree = HexagonCover.NBand.M8500_8700.SplitData.node0064 := by
  change Tree.branch (151 : Fin 175) _ = Tree.branch (151 : Fin 175) _
  apply congrArg (Tree.branch (151 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0134

def B0150 : Block := .branch 170 ![36346078628713813621116163871211905, 309485009821345618480596482, 130601767450242908029982724, 5846006897772755399855725917360730088754378727432, 94778167094404185458843656112321848441667600, 982134831577882783403023582264938259837693706240032, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 497).pointIds 497), (.leaf 1 (Common.fact 505).pointIds 505), (.leaf 2 (Common.fact 487).pointIds 487), (.leaf 3 (Common.fact 560).pointIds 560), (.leaf 4 (Common.fact 561).pointIds 561), (.leaf 5 (Common.fact 562).pointIds 562), (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq0150 : B0150.tree = HexagonCover.NBand.M8500_8700.SplitData.node0150 := by
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

def B0149 : Block := .branch 169 ![36346078628713813621116163871211905, 309485009821345618480596482, 130601767450242908029982724, 5846006897772755399855725917360730088754378727432, 94778167094404185458843656112321848441667600, 233845993264460489282736947914201353773856244236320, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 499).pointIds 499), (.leaf 1 (Common.fact 506).pointIds 506), (.leaf 2 (Common.fact 490).pointIds 490), (.leaf 3 (Common.fact 558).pointIds 558), (.leaf 4 (Common.fact 559).pointIds 559), B0150, (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq0149 : B0149.tree = HexagonCover.NBand.M8500_8700.SplitData.node0149 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0150
  · rfl

def B0148 : Block := .branch 87 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 5846006897772755399855725917360730088754378727432, 94778167094404185458843656112321848441667600, 233845993264460489282736947914201353773856244236320, 385836443449329647932829607236202725091092001718336] ![(.leaf 0 (Common.fact 378).pointIds 378), (.leaf 1 (Common.fact 379).pointIds 379), B0149, (.leaf 3 (Common.fact 556).pointIds 556), (.leaf 4 (Common.fact 381).pointIds 381), (.leaf 5 (Common.fact 382).pointIds 382), (.leaf 6 (Common.fact 557).pointIds 557)]
theorem treeEq0148 : B0148.tree = HexagonCover.NBand.M8500_8700.SplitData.node0148 := by
  change Tree.branch (87 : Fin 175) _ = Tree.branch (87 : Fin 175) _
  apply congrArg (Tree.branch (87 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0149
  · rfl
  · rfl
  · rfl
  · rfl

def B0147 : Block := .branch 171 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 5992156713405151108362148800723255978599454074757128, 94778167094404185458843656112321848441667600, 233845993264460489282736947914201353773856244236320, 385836443449329647932829607236202725091092001718336] ![(.leaf 0 (Common.fact 496).pointIds 496), (.leaf 1 (Common.fact 504).pointIds 504), (.leaf 2 (Common.fact 478).pointIds 478), (.leaf 3 (Common.fact 553).pointIds 553), (.leaf 4 (Common.fact 554).pointIds 554), (.leaf 5 (Common.fact 555).pointIds 555), B0148]
theorem treeEq0147 : B0147.tree = HexagonCover.NBand.M8500_8700.SplitData.node0147 := by
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
  · exact treeEq0148

def B0146 : Block := .branch 172 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 5846006897772755399855725917360730088754378727432, 94778167094404185458843656112321848441667600, 233845993264460489282736947914201353773856244236320, 385836443449329647932829607236202725091092001718336] ![(.leaf 0 (Common.fact 494).pointIds 494), (.leaf 1 (Common.fact 502).pointIds 502), (.leaf 2 (Common.fact 480).pointIds 480), B0147, (.leaf 4 (Common.fact 551).pointIds 551), (.leaf 5 (Common.fact 552).pointIds 552), (.leaf 6 (Common.fact 471).pointIds 471)]
theorem treeEq0146 : B0146.tree = HexagonCover.NBand.M8500_8700.SplitData.node0146 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0147
  · rfl
  · rfl
  · rfl

def B0145 : Block := .branch 168 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 5846006897772755399855725917360730088754378727432, 94778167094404185458843656112321848441667600, 233845993264460489282736947914201353773856244236320, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 493).pointIds 493), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 477).pointIds 477), (.leaf 3 (Common.fact 548).pointIds 548), (.leaf 4 (Common.fact 549).pointIds 549), (.leaf 5 (Common.fact 550).pointIds 550), B0146]
theorem treeEq0145 : B0145.tree = HexagonCover.NBand.M8500_8700.SplitData.node0145 := by
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
  · exact treeEq0146

def B0144 : Block := .branch 162 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 348449143727040986586495598010130648555528, 94778167094404185458843656112321848441667600, 233845993264460489282736947914201353773856244236320, 11692024325285608097096382553318234372623019016256] ![(.leaf 0 (Common.fact 373).pointIds 373), (.leaf 1 (Common.fact 374).pointIds 374), (.leaf 2 (Common.fact 375).pointIds 375), B0145, (.leaf 4 (Common.fact 547).pointIds 547), (.leaf 5 (Common.fact 376).pointIds 376), (.leaf 6 (Common.fact 377).pointIds 377)]
theorem treeEq0144 : B0144.tree = HexagonCover.NBand.M8500_8700.SplitData.node0144 := by
  change Tree.branch (162 : Fin 175) _ = Tree.branch (162 : Fin 175) _
  apply congrArg (Tree.branch (162 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0145
  · rfl
  · rfl
  · rfl

def B0143 : Block := .branch 152 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 348449143727040986586495598010130648555528, 96171963669312349405189638504362371035791376, 233840284273689665443212714770323555793310713249824, 11692024325285608097096382553318234372623019016256] ![(.leaf 0 (Common.fact 354).pointIds 354), (.leaf 1 (Common.fact 355).pointIds 355), (.leaf 2 (Common.fact 356).pointIds 356), (.leaf 3 (Common.fact 357).pointIds 357), (.leaf 4 (Common.fact 358).pointIds 358), B0144, (.leaf 6 (Common.fact 546).pointIds 546)]
theorem treeEq0143 : B0143.tree = HexagonCover.NBand.M8500_8700.SplitData.node0143 := by
  change Tree.branch (152 : Fin 175) _ = Tree.branch (152 : Fin 175) _
  apply congrArg (Tree.branch (152 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0144
  · rfl

def B0142 : Block := .branch 163 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 348449143727040986586495598010130648555528, 96171963669312349405189638504362371035791376, 233840284273689665443212714770323555793310713249824, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 545).pointIds 545), (.leaf 5 (Common.fact 387).pointIds 387), B0143]
theorem treeEq0142 : B0142.tree = HexagonCover.NBand.M8500_8700.SplitData.node0142 := by
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
  · exact treeEq0143

def B0141 : Block := .branch 165 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 348449143727040986586495598010130648555528, 96171963669312349405189638504362371035791376, 187072231879100772060694800123402499164320871874592, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 544).pointIds 544), B0142, (.leaf 0 [] 0)]
theorem treeEq0141 : B0141.tree = HexagonCover.NBand.M8500_8700.SplitData.node0141 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0142
  · rfl

def B0140 : Block := .branch 167 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 348449143727040986586495598010130648555528, 96171963669312349405189638504362371035791376, 22300745198530623141535718272648361506373664, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 542).pointIds 542), B0141, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq0140 : B0140.tree = HexagonCover.NBand.M8500_8700.SplitData.node0140 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0141
  · rfl

def B0063 : Block := .branch 146 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 348449143727357899236552655360504824356872, 6968982875189856839046765413768925011869712, 22300745198530623141535718272648361506373664, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 347).pointIds 347), B0064, B0140, (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 0 [] 0)]
theorem treeEq0063 : B0063.tree = HexagonCover.NBand.M8500_8700.SplitData.node0063 := by
  change Tree.branch (146 : Fin 175) _ = Tree.branch (146 : Fin 175) _
  apply congrArg (Tree.branch (146 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0064
  · exact treeEq0140
  · rfl
  · rfl

theorem accepted0063 : B0063.accepted = true := by decide +kernel
theorem checked0063 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node0063 (maskNeeds ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 348449143727357899236552655360504824356872, 6968982875189856839046765413768925011869712, 22300745198530623141535718272648361506373664, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq0063]
  exact B0063.sound accepted0063
#print axioms checked0063

def Tip0061_0063 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node0063 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 348449143727357899236552655360504824356872, 6968982875189856839046765413768925011869712, 22300745198530623141535718272648361506373664, 11226638384751466903891587970215375558672448] checked0063
def B0154 : Block := .branch 172 ![36346078628713813621116163871211905, 309485009821345618480596482, 130601767450242908029982724, 2993155442456669970603639103545820714848795871961096, 11692018673833522978285264045659832319337836937232, 393248, 33451160333091799829611510330799020985286720] ![(.leaf 0 (Common.fact 494).pointIds 494), (.leaf 1 (Common.fact 502).pointIds 502), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 525).pointIds 525), (.leaf 4 (Common.fact 568).pointIds 568), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 570).pointIds 570)]
theorem treeEq0154 : B0154.tree = HexagonCover.NBand.M8500_8700.SplitData.node0154 := by
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

def B0153 : Block := .branch 171 ![36346078628713813621116163871211905, 309485009821345618480596482, 130601767450242908029982724, 89202980794122492566142873090593446023946248, 11692018673833522978285264045659832319337836937232, 393248, 33451160333091799829611510330799020985286720] ![(.leaf 0 (Common.fact 496).pointIds 496), (.leaf 1 (Common.fact 504).pointIds 504), (.leaf 2 (Common.fact 478).pointIds 478), B0154, (.leaf 4 (Common.fact 565).pointIds 565), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 567).pointIds 567)]
theorem treeEq0153 : B0153.tree = HexagonCover.NBand.M8500_8700.SplitData.node0153 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0154
  · rfl
  · rfl
  · rfl

def B0152 : Block := .branch 146 ![36346078628713813621116163871211905, 309485009821345618480596482, 130601767450242908029982724, 24584, 11692018673833522978285264045659832319337836937232, 393248, 33451160333091799829611510330799020985286720] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 347).pointIds 347), B0153, (.leaf 4 (Common.fact 564).pointIds 564), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 0 [] 0)]
theorem treeEq0152 : B0152.tree = HexagonCover.NBand.M8500_8700.SplitData.node0152 := by
  change Tree.branch (146 : Fin 175) _ = Tree.branch (146 : Fin 175) _
  apply congrArg (Tree.branch (146 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0153
  · rfl
  · rfl
  · rfl

def B0151 : Block := .branch 163 ![36346078628713813621116163871211905, 309485009821345618480596482, 130601767450242908029982724, 24584, 5575186299632655785383929568162090376593424, 393248, 33451160333091799829611510330799020985286720] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), B0152, (.leaf 5 (Common.fact 387).pointIds 387), (.leaf 6 (Common.fact 563).pointIds 563)]
theorem treeEq0151 : B0151.tree = HexagonCover.NBand.M8500_8700.SplitData.node0151 := by
  change Tree.branch (163 : Fin 175) _ = Tree.branch (163 : Fin 175) _
  apply congrArg (Tree.branch (163 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0152
  · rfl
  · rfl

def B0062 : Block := .branch 144 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 348449143727357899236552655360504824356872, 6968982875189856839046765413768925011869712, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 340).pointIds 340), (.leaf 1 (Common.fact 341).pointIds 341), (.leaf 2 (Common.fact 342).pointIds 342), (.leaf 3 (Common.fact 343).pointIds 343), (.leaf 4 (Common.fact 344).pointIds 344), Tip0061_0063, B0151]
theorem treeEq0062 : B0062.tree = HexagonCover.NBand.M8500_8700.SplitData.node0062 := by
  change Tree.branch (144 : Fin 175) _ = Tree.branch (144 : Fin 175) _
  apply congrArg (Tree.branch (144 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0151

def B0160 : Block := .branch 169 ![36346078628713813621116163871211905, 309485009821345618480596482, 130601767450242908029982724, 348449143727357899236552655360504824356872, 5444518519772122732267447285220332634128, 1496577676626844588240573268701473812127674924400672, 3367299789179515365405137334053416731525355794858048] ![(.leaf 0 (Common.fact 499).pointIds 499), (.leaf 1 (Common.fact 506).pointIds 506), (.leaf 2 (Common.fact 490).pointIds 490), (.leaf 3 (Common.fact 584).pointIds 584), (.leaf 4 (Common.fact 585).pointIds 585), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 586).pointIds 586)]
theorem treeEq0160 : B0160.tree = HexagonCover.NBand.M8500_8700.SplitData.node0160 := by
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

def B0159 : Block := .branch 170 ![36346078628713813621116163871211905, 309485009821345618480596482, 130601767450242908029982724, 348449143727357899236552655360504824356872, 5444518519772122732267447285220332634128, 393248, 3367299789179515365405137334053416731525355794858048] ![(.leaf 0 (Common.fact 497).pointIds 497), (.leaf 1 (Common.fact 505).pointIds 505), (.leaf 2 (Common.fact 487).pointIds 487), (.leaf 3 (Common.fact 581).pointIds 581), (.leaf 4 (Common.fact 582).pointIds 582), B0160, (.leaf 6 (Common.fact 583).pointIds 583)]
theorem treeEq0159 : B0159.tree = HexagonCover.NBand.M8500_8700.SplitData.node0159 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0160
  · rfl

def B0158 : Block := .branch 171 ![36346078628713813621116163871211905, 309485009821345618480596482, 130601767450242908029982724, 5986310706855827496689650974042447903871204520386568, 5444518519772122732267447285220332634128, 5708990770823839524233143877797980545531379744, 374144435925826188923990796650469107270005946843200] ![(.leaf 0 (Common.fact 496).pointIds 496), (.leaf 1 (Common.fact 504).pointIds 504), (.leaf 2 (Common.fact 478).pointIds 478), (.leaf 3 (Common.fact 578).pointIds 578), (.leaf 4 (Common.fact 579).pointIds 579), (.leaf 5 (Common.fact 580).pointIds 580), B0159]
theorem treeEq0158 : B0158.tree = HexagonCover.NBand.M8500_8700.SplitData.node0158 := by
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
  · exact treeEq0159

def B0157 : Block := .branch 172 ![36346078628713813621116163871211905, 309485009821345618480596482, 130601767450242908029982724, 348449143727357899236552655360504824356872, 5444518519772122732267447285220332634128, 5708990770823839524233143877797980545531379744, 374144435925826188923990796650469107270005946843200] ![(.leaf 0 (Common.fact 494).pointIds 494), (.leaf 1 (Common.fact 502).pointIds 502), (.leaf 2 (Common.fact 480).pointIds 480), B0158, (.leaf 4 (Common.fact 575).pointIds 575), (.leaf 5 (Common.fact 576).pointIds 576), (.leaf 6 (Common.fact 577).pointIds 577)]
theorem treeEq0157 : B0157.tree = HexagonCover.NBand.M8500_8700.SplitData.node0157 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0158
  · rfl
  · rfl
  · rfl

def B0156 : Block := .branch 168 ![36346078628713813621116163871211905, 309485009821345618480596482, 130601767450242908029982724, 348449143727357899236552655360504824356872, 5444518519772122732267447285220332634128, 5708990770823839524233143877797980545531379744, 16769115041863847479475100654238087215841344] ![(.leaf 0 (Common.fact 493).pointIds 493), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 477).pointIds 477), (.leaf 3 (Common.fact 572).pointIds 572), (.leaf 4 (Common.fact 573).pointIds 573), (.leaf 5 (Common.fact 574).pointIds 574), B0157]
theorem treeEq0156 : B0156.tree = HexagonCover.NBand.M8500_8700.SplitData.node0156 := by
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
  · exact treeEq0157

def B0155 : Block := .branch 152 ![36346078628713813621116163871211905, 309485009821345618480596482, 130601767450242908029982724, 348449143727357899236552655360504824356872, 1399241093427936069078249839325742926757904, 393248, 16769157577159712596783033576064016186867776] ![(.leaf 0 (Common.fact 354).pointIds 354), (.leaf 1 (Common.fact 355).pointIds 355), (.leaf 2 (Common.fact 356).pointIds 356), (.leaf 3 (Common.fact 357).pointIds 357), (.leaf 4 (Common.fact 358).pointIds 358), B0156, (.leaf 6 (Common.fact 571).pointIds 571)]
theorem treeEq0155 : B0155.tree = HexagonCover.NBand.M8500_8700.SplitData.node0155 := by
  change Tree.branch (152 : Fin 175) _ = Tree.branch (152 : Fin 175) _
  apply congrArg (Tree.branch (152 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0156
  · rfl

def B0061 : Block := .branch 142 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 348449143727357899236552655360504824356872, 1399241093427936069078249839325742926757904, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), B0062, (.leaf 5 (Common.fact 339).pointIds 339), B0155]
theorem treeEq0061 : B0061.tree = HexagonCover.NBand.M8500_8700.SplitData.node0061 := by
  change Tree.branch (142 : Fin 175) _ = Tree.branch (142 : Fin 175) _
  apply congrArg (Tree.branch (142 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0062
  · rfl
  · exact treeEq0155

theorem accepted0061 : B0061.accepted = true := by decide +kernel
theorem checked0061 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node0061 (maskNeeds ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 348449143727357899236552655360504824356872, 1399241093427936069078249839325742926757904, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq0061]
  exact B0061.sound accepted0061
#print axioms checked0061

def Tip0060_0061 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node0061 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 348449143727357899236552655360504824356872, 1399241093427936069078249839325742926757904, 393248, 11226638384751466903891587970215375558672448] checked0061
def B0172 : Block := .branch 170 ![36346078628713813621116163871211905, 309485009821345618480596482, 130601767450242908029982724, 5846006550004176406656616257791881293487266619400, 353893662246813109318763045295350981165072, 982134831577882783403023582264938259837693706240032, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 497).pointIds 497), (.leaf 1 (Common.fact 505).pointIds 505), (.leaf 2 (Common.fact 487).pointIds 487), (.leaf 3 (Common.fact 600).pointIds 600), (.leaf 4 (Common.fact 601).pointIds 601), (.leaf 5 (Common.fact 562).pointIds 562), (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq0172 : B0172.tree = HexagonCover.NBand.M8500_8700.SplitData.node0172 := by
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

def B0171 : Block := .branch 169 ![36346078628713813621116163871211905, 309485009821345618480596482, 130601767450242908029982724, 5846006550004176406656616257791881293487266619400, 353893662246813109318763045295350981165072, 233845993264460489282736947914201353773856244236320, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 499).pointIds 499), (.leaf 1 (Common.fact 506).pointIds 506), (.leaf 2 (Common.fact 490).pointIds 490), (.leaf 3 (Common.fact 598).pointIds 598), (.leaf 4 (Common.fact 599).pointIds 599), B0172, (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq0171 : B0171.tree = HexagonCover.NBand.M8500_8700.SplitData.node0171 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0172
  · rfl

def B0170 : Block := .branch 87 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 5846006550004176406656616257791881293487266619400, 353893662246813109318763045295350981165072, 233845993264460489282736947914201353773856244236320, 385836443449329647932829607236202725091092001718336] ![(.leaf 0 (Common.fact 378).pointIds 378), (.leaf 1 (Common.fact 379).pointIds 379), B0171, (.leaf 3 (Common.fact 597).pointIds 597), (.leaf 4 (Common.fact 381).pointIds 381), (.leaf 5 (Common.fact 382).pointIds 382), (.leaf 6 (Common.fact 557).pointIds 557)]
theorem treeEq0170 : B0170.tree = HexagonCover.NBand.M8500_8700.SplitData.node0170 := by
  change Tree.branch (87 : Fin 175) _ = Tree.branch (87 : Fin 175) _
  apply congrArg (Tree.branch (87 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0171
  · rfl
  · rfl
  · rfl
  · rfl

def B0169 : Block := .branch 171 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 5992156713057382529368949691063687129804186962649096, 353893662246813109318763045295350981165072, 233845993264460489282736947914201353773856244236320, 385836443449329647932829607236202725091092001718336] ![(.leaf 0 (Common.fact 496).pointIds 496), (.leaf 1 (Common.fact 504).pointIds 504), (.leaf 2 (Common.fact 478).pointIds 478), (.leaf 3 (Common.fact 595).pointIds 595), (.leaf 4 (Common.fact 596).pointIds 596), (.leaf 5 (Common.fact 555).pointIds 555), B0170]
theorem treeEq0169 : B0169.tree = HexagonCover.NBand.M8500_8700.SplitData.node0169 := by
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
  · exact treeEq0170

def B0168 : Block := .branch 172 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 5846006550004176406656616257791881293487266619400, 353893662246813109318763045295350981165072, 233845993264460489282736947914201353773856244236320, 385836443449329647932829607236202725091092001718336] ![(.leaf 0 (Common.fact 494).pointIds 494), (.leaf 1 (Common.fact 502).pointIds 502), (.leaf 2 (Common.fact 480).pointIds 480), B0169, (.leaf 4 (Common.fact 594).pointIds 594), (.leaf 5 (Common.fact 552).pointIds 552), (.leaf 6 (Common.fact 471).pointIds 471)]
theorem treeEq0168 : B0168.tree = HexagonCover.NBand.M8500_8700.SplitData.node0168 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0169
  · rfl
  · rfl
  · rfl

def B0167 : Block := .branch 168 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 5846006550004176406656616257791881293487266619400, 353893662246813109318763045295350981165072, 233845993264460489282736947914201353773856244236320, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 493).pointIds 493), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 477).pointIds 477), (.leaf 3 (Common.fact 592).pointIds 592), (.leaf 4 (Common.fact 593).pointIds 593), (.leaf 5 (Common.fact 550).pointIds 550), B0168]
theorem treeEq0167 : B0167.tree = HexagonCover.NBand.M8500_8700.SplitData.node0167 := by
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
  · exact treeEq0168

def B0166 : Block := .branch 162 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 680564733841876926926749214863536447496, 353893662246813109318763045295350981165072, 233845993264460489282736947914201353773856244236320, 11692024325285608097096382553318234372623019016256] ![(.leaf 0 (Common.fact 373).pointIds 373), (.leaf 1 (Common.fact 374).pointIds 374), (.leaf 2 (Common.fact 375).pointIds 375), B0167, (.leaf 4 (Common.fact 591).pointIds 591), (.leaf 5 (Common.fact 376).pointIds 376), (.leaf 6 (Common.fact 377).pointIds 377)]
theorem treeEq0166 : B0166.tree = HexagonCover.NBand.M8500_8700.SplitData.node0166 := by
  change Tree.branch (162 : Fin 175) _ = Tree.branch (162 : Fin 175) _
  apply congrArg (Tree.branch (162 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0167
  · rfl
  · rfl
  · rfl

def B0165 : Block := .branch 144 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 680564733841876926926749214863536447496, 353893662246813109318763045295350981165072, 233845970963715290752113806378483081125494738255904, 11692024325285608097096382553318234372623019016256] ![(.leaf 0 (Common.fact 340).pointIds 340), (.leaf 1 (Common.fact 341).pointIds 341), (.leaf 2 (Common.fact 342).pointIds 342), (.leaf 3 (Common.fact 343).pointIds 343), (.leaf 4 (Common.fact 344).pointIds 344), B0166, (.leaf 6 (Common.fact 590).pointIds 590)]
theorem treeEq0165 : B0165.tree = HexagonCover.NBand.M8500_8700.SplitData.node0165 := by
  change Tree.branch (144 : Fin 175) _ = Tree.branch (144 : Fin 175) _
  apply congrArg (Tree.branch (144 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0166
  · rfl

def B0164 : Block := .branch 152 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 680564733841876926926749214863536447496, 1747690237154977055664745437335873575288848, 233840261972944466912589573234605283144949207269408, 11692024325285608097096382553318234372623019016256] ![(.leaf 0 (Common.fact 354).pointIds 354), (.leaf 1 (Common.fact 355).pointIds 355), (.leaf 2 (Common.fact 356).pointIds 356), (.leaf 3 (Common.fact 357).pointIds 357), (.leaf 4 (Common.fact 358).pointIds 358), B0165, (.leaf 6 (Common.fact 546).pointIds 546)]
theorem treeEq0164 : B0164.tree = HexagonCover.NBand.M8500_8700.SplitData.node0164 := by
  change Tree.branch (152 : Fin 175) _ = Tree.branch (152 : Fin 175) _
  apply congrArg (Tree.branch (152 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0165
  · rfl

def B0163 : Block := .branch 163 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 680564733841876926926749214863536447496, 1747690237154977055664745437335873575288848, 233840261972944466912589573234605283144949207269408, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 589).pointIds 589), (.leaf 5 (Common.fact 387).pointIds 387), B0164]
theorem treeEq0163 : B0163.tree = HexagonCover.NBand.M8500_8700.SplitData.node0163 := by
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
  · exact treeEq0164

def B0162 : Block := .branch 165 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 680564733841876926926749214863536447496, 1747690237154977055664745437335873575288848, 187072209578355573530071658587684226515959365894176, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 588).pointIds 588), B0163, (.leaf 0 [] 0)]
theorem treeEq0162 : B0162.tree = HexagonCover.NBand.M8500_8700.SplitData.node0162 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0163
  · rfl

def B0161 : Block := .branch 167 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 680564733841876926926749214863536447496, 1747690237154977055664745437335873575288848, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 587).pointIds 587), B0162, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq0161 : B0161.tree = HexagonCover.NBand.M8500_8700.SplitData.node0161 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0162
  · rfl

def B0060 : Block := .branch 138 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 680564734158789576983806565237712248840, 1399241093427936069078249839325742926757904, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), Tip0060_0061, B0161, (.leaf 5 (Common.fact 333).pointIds 333), (.leaf 6 (Common.fact 334).pointIds 334)]
theorem treeEq0060 : B0060.tree = HexagonCover.NBand.M8500_8700.SplitData.node0060 := by
  change Tree.branch (138 : Fin 175) _ = Tree.branch (138 : Fin 175) _
  apply congrArg (Tree.branch (138 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0161
  · rfl
  · rfl

theorem accepted0060 : B0060.accepted = true := by decide +kernel
theorem checked0060 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node0060 (maskNeeds ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 680564734158789576983806565237712248840, 1399241093427936069078249839325742926757904, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq0060]
  exact B0060.sound accepted0060
#print axioms checked0060

def B0191 : Block := .branch 170 ![36346078628713813621116163871211905, 309485009821345618480596482, 130601767450242908029982724, 5846006549324276286812631788801583982153870368776, 683223838870554075526010395296138362896, 982134831577882783403023582264938259837693706240032, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 497).pointIds 497), (.leaf 1 (Common.fact 505).pointIds 505), (.leaf 2 (Common.fact 487).pointIds 487), (.leaf 3 (Common.fact 628).pointIds 628), (.leaf 4 (Common.fact 629).pointIds 629), (.leaf 5 (Common.fact 562).pointIds 562), (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq0191 : B0191.tree = HexagonCover.NBand.M8500_8700.SplitData.node0191 := by
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

def B0190 : Block := .branch 169 ![36346078628713813621116163871211905, 309485009821345618480596482, 130601767450242908029982724, 5846006549324276286812631788801583982153870368776, 683223838870554075526010395296138362896, 233845993264460489282736947914201353773856244236320, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 499).pointIds 499), (.leaf 1 (Common.fact 506).pointIds 506), (.leaf 2 (Common.fact 490).pointIds 490), (.leaf 3 (Common.fact 626).pointIds 626), (.leaf 4 (Common.fact 627).pointIds 627), B0191, (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq0190 : B0190.tree = HexagonCover.NBand.M8500_8700.SplitData.node0190 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0191
  · rfl

def B0189 : Block := .branch 87 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 5846006549324276286812631788801583982153870368776, 683223838870554075526010395296138362896, 233845993264460489282736947914201353773856244236320, 385836443449329647932829607236202725091092001718336] ![(.leaf 0 (Common.fact 378).pointIds 378), (.leaf 1 (Common.fact 379).pointIds 379), B0190, (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 381).pointIds 381), (.leaf 5 (Common.fact 382).pointIds 382), (.leaf 6 (Common.fact 557).pointIds 557)]
theorem treeEq0189 : B0189.tree = HexagonCover.NBand.M8500_8700.SplitData.node0189 := by
  change Tree.branch (87 : Fin 175) _ = Tree.branch (87 : Fin 175) _
  apply congrArg (Tree.branch (87 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0190
  · rfl
  · rfl
  · rfl
  · rfl

def B0188 : Block := .branch 171 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 5992156713056702629249105706594696832492853566398472, 683223838870554075526010395296138362896, 233845993264460489282736947914201353773856244236320, 385836443449329647932829607236202725091092001718336] ![(.leaf 0 (Common.fact 496).pointIds 496), (.leaf 1 (Common.fact 504).pointIds 504), (.leaf 2 (Common.fact 478).pointIds 478), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 624).pointIds 624), (.leaf 5 (Common.fact 555).pointIds 555), B0189]
theorem treeEq0188 : B0188.tree = HexagonCover.NBand.M8500_8700.SplitData.node0188 := by
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
  · exact treeEq0189

def B0187 : Block := .branch 172 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 5846006549324276286812631788801583982153870368776, 683223838870554075526010395296138362896, 233845993264460489282736947914201353773856244236320, 385836443449329647932829607236202725091092001718336] ![(.leaf 0 (Common.fact 494).pointIds 494), (.leaf 1 (Common.fact 502).pointIds 502), (.leaf 2 (Common.fact 480).pointIds 480), B0188, (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 552).pointIds 552), (.leaf 6 (Common.fact 471).pointIds 471)]
theorem treeEq0187 : B0187.tree = HexagonCover.NBand.M8500_8700.SplitData.node0187 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0188
  · rfl
  · rfl
  · rfl

def B0186 : Block := .branch 168 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 5846006549324276286812631788801583982153870368776, 683223838870554075526010395296138362896, 233845993264460489282736947914201353773856244236320, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 493).pointIds 493), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 477).pointIds 477), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 621).pointIds 621), (.leaf 5 (Common.fact 550).pointIds 550), B0187]
theorem treeEq0186 : B0186.tree = HexagonCover.NBand.M8500_8700.SplitData.node0186 := by
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
  · exact treeEq0187

def B0185 : Block := .branch 162 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 664613997892457936451903530140196872, 683223838870554075526010395296138362896, 233845993264460489282736947914201353773856244236320, 11692024325285608097096382553318234372623019016256] ![(.leaf 0 (Common.fact 373).pointIds 373), (.leaf 1 (Common.fact 374).pointIds 374), (.leaf 2 (Common.fact 375).pointIds 375), B0186, (.leaf 4 (Common.fact 619).pointIds 619), (.leaf 5 (Common.fact 376).pointIds 376), (.leaf 6 (Common.fact 377).pointIds 377)]
theorem treeEq0185 : B0185.tree = HexagonCover.NBand.M8500_8700.SplitData.node0185 := by
  change Tree.branch (162 : Fin 175) _ = Tree.branch (162 : Fin 175) _
  apply congrArg (Tree.branch (162 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0186
  · rfl
  · rfl
  · rfl

def B0184 : Block := .branch 144 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 664613997892457936451903530140196872, 683223838870554075526010395296138362896, 233845970963715290752113806378483081125494738255904, 11692024325285608097096382553318234372623019016256] ![(.leaf 0 (Common.fact 340).pointIds 340), (.leaf 1 (Common.fact 341).pointIds 341), (.leaf 2 (Common.fact 342).pointIds 342), (.leaf 3 (Common.fact 343).pointIds 343), (.leaf 4 (Common.fact 344).pointIds 344), B0185, (.leaf 6 (Common.fact 590).pointIds 590)]
theorem treeEq0184 : B0184.tree = HexagonCover.NBand.M8500_8700.SplitData.node0184 := by
  change Tree.branch (144 : Fin 175) _ = Tree.branch (144 : Fin 175) _
  apply congrArg (Tree.branch (144 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0185
  · rfl

def B0183 : Block := .branch 152 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 664613997892457936451903530140196872, 1394479798747034500421508402435818732486672, 233840261972944466912589573234605283144949207269408, 11692024325285608097096382553318234372623019016256] ![(.leaf 0 (Common.fact 354).pointIds 354), (.leaf 1 (Common.fact 355).pointIds 355), (.leaf 2 (Common.fact 356).pointIds 356), (.leaf 3 (Common.fact 357).pointIds 357), (.leaf 4 (Common.fact 358).pointIds 358), B0184, (.leaf 6 (Common.fact 546).pointIds 546)]
theorem treeEq0183 : B0183.tree = HexagonCover.NBand.M8500_8700.SplitData.node0183 := by
  change Tree.branch (152 : Fin 175) _ = Tree.branch (152 : Fin 175) _
  apply congrArg (Tree.branch (152 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0184
  · rfl

def B0182 : Block := .branch 163 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 664613997892457936451903530140196872, 1394479798747034500421508402435818732486672, 233840261972944466912589573234605283144949207269408, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 618).pointIds 618), (.leaf 5 (Common.fact 387).pointIds 387), B0183]
theorem treeEq0182 : B0182.tree = HexagonCover.NBand.M8500_8700.SplitData.node0182 := by
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
  · exact treeEq0183

def B0181 : Block := .branch 165 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 664613997892457936451903530140196872, 1394479798747034500421508402435818732486672, 187072209578355573530071658587684226515959365894176, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 617).pointIds 617), B0182, (.leaf 0 [] 0)]
theorem treeEq0181 : B0181.tree = HexagonCover.NBand.M8500_8700.SplitData.node0181 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0182
  · rfl

def B0180 : Block := .branch 167 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 664613997892457936451903530140196872, 1394479798747034500421508402435818732486672, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 616).pointIds 616), B0181, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq0180 : B0180.tree = HexagonCover.NBand.M8500_8700.SplitData.node0180 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0181
  · rfl

theorem accepted0180 : B0180.accepted = true := by decide +kernel
theorem checked0180 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node0180 (maskNeeds ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 664613997892457936451903530140196872, 1394479798747034500421508402435818732486672, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq0180]
  exact B0180.sound accepted0180
#print axioms checked0180

def Tip0057_0060 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node0060 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 680564734158789576983806565237712248840, 1399241093427936069078249839325742926757904, 393248, 11226638384751466903891587970215375558672448] checked0060
def Tip0057_0180 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node0180 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 664613997892457936451903530140196872, 1394479798747034500421508402435818732486672, 393248, 11226638384751466903891587970215375558672448] checked0180
def B0179 : Block := .branch 169 ![36346078628713813621116163871211905, 309485009821345618480596482, 130601767450242908029982724, 680564734158789576983806565237712248840, 2659105028677148599261180432601939984, 1496577676626844588240573268701473812127674924400672, 3367299783609773583643216564084901157082173709746240] ![(.leaf 0 (Common.fact 499).pointIds 499), (.leaf 1 (Common.fact 506).pointIds 506), (.leaf 2 (Common.fact 490).pointIds 490), (.leaf 3 (Common.fact 613).pointIds 613), (.leaf 4 (Common.fact 614).pointIds 614), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 615).pointIds 615)]
theorem treeEq0179 : B0179.tree = HexagonCover.NBand.M8500_8700.SplitData.node0179 := by
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

def B0178 : Block := .branch 170 ![36346078628713813621116163871211905, 309485009821345618480596482, 130601767450242908029982724, 680564734158789576983806565237712248840, 2659105028677148599261180432601939984, 393248, 3367299783609773583643216564084901157082173709746240] ![(.leaf 0 (Common.fact 497).pointIds 497), (.leaf 1 (Common.fact 505).pointIds 505), (.leaf 2 (Common.fact 487).pointIds 487), (.leaf 3 (Common.fact 610).pointIds 610), (.leaf 4 (Common.fact 611).pointIds 611), B0179, (.leaf 6 (Common.fact 612).pointIds 612)]
theorem treeEq0178 : B0178.tree = HexagonCover.NBand.M8500_8700.SplitData.node0178 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0179
  · rfl

def B0177 : Block := .branch 171 ![36346078628713813621116163871211905, 309485009821345618480596482, 130601767450242908029982724, 5986310706508058917696451864382879055075937408278536, 2659105028677148599261180432601939984, 5731291516022370147374679596070628907037360160, 374144430356084407162070026681953532826823861731392] ![(.leaf 0 (Common.fact 496).pointIds 496), (.leaf 1 (Common.fact 504).pointIds 504), (.leaf 2 (Common.fact 478).pointIds 478), (.leaf 3 (Common.fact 608).pointIds 608), (.leaf 4 (Common.fact 609).pointIds 609), (.leaf 5 (Common.fact 430).pointIds 430), B0178]
theorem treeEq0177 : B0177.tree = HexagonCover.NBand.M8500_8700.SplitData.node0177 := by
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
  · exact treeEq0178

def B0176 : Block := .branch 172 ![36346078628713813621116163871211905, 309485009821345618480596482, 130601767450242908029982724, 680564734158789576983806565237712248840, 2659105028677148599261180432601939984, 5731291516022370147374679596070628907037360160, 374144430356084407162070026681953532826823861731392] ![(.leaf 0 (Common.fact 494).pointIds 494), (.leaf 1 (Common.fact 502).pointIds 502), (.leaf 2 (Common.fact 480).pointIds 480), B0177, (.leaf 4 (Common.fact 606).pointIds 606), (.leaf 5 (Common.fact 432).pointIds 432), (.leaf 6 (Common.fact 607).pointIds 607)]
theorem treeEq0176 : B0176.tree = HexagonCover.NBand.M8500_8700.SplitData.node0176 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0177
  · rfl
  · rfl
  · rfl

def B0175 : Block := .branch 168 ![36346078628713813621116163871211905, 309485009821345618480596482, 130601767450242908029982724, 680564734158789576983806565237712248840, 2659105028677148599261180432601939984, 5731291516022370147374679596070628907037360160, 11199373260101926709506585079794905130729536] ![(.leaf 0 (Common.fact 493).pointIds 493), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 477).pointIds 477), (.leaf 3 (Common.fact 604).pointIds 604), (.leaf 4 (Common.fact 605).pointIds 605), (.leaf 5 (Common.fact 405).pointIds 405), B0176]
theorem treeEq0175 : B0175.tree = HexagonCover.NBand.M8500_8700.SplitData.node0175 := by
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
  · exact treeEq0176

def B0174 : Block := .branch 144 ![36346078628713813621116163871211905, 309485009821345618480596482, 130601767450242908029982724, 680564734158789576983806565237712248840, 2659105028677148599261180432601939984, 5708990770823839524233143877797980545531379744, 11199415795397791826814518001620834101755968] ![(.leaf 0 (Common.fact 340).pointIds 340), (.leaf 1 (Common.fact 341).pointIds 341), (.leaf 2 (Common.fact 342).pointIds 342), (.leaf 3 (Common.fact 343).pointIds 343), (.leaf 4 (Common.fact 344).pointIds 344), B0175, (.leaf 6 (Common.fact 603).pointIds 603)]
theorem treeEq0174 : B0174.tree = HexagonCover.NBand.M8500_8700.SplitData.node0174 := by
  change Tree.branch (144 : Fin 175) _ = Tree.branch (144 : Fin 175) _
  apply congrArg (Tree.branch (144 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0175
  · rfl

def B0173 : Block := .branch 152 ![36346078628713813621116163871211905, 309485009821345618480596482, 130601767450242908029982724, 680564734158789576983806565237712248840, 1393799234013192623494581653220955196063760, 393248, 11199415795397791826814518001620834101755968] ![(.leaf 0 (Common.fact 354).pointIds 354), (.leaf 1 (Common.fact 355).pointIds 355), (.leaf 2 (Common.fact 356).pointIds 356), (.leaf 3 (Common.fact 357).pointIds 357), (.leaf 4 (Common.fact 358).pointIds 358), B0174, (.leaf 6 (Common.fact 602).pointIds 602)]
theorem treeEq0173 : B0173.tree = HexagonCover.NBand.M8500_8700.SplitData.node0173 := by
  change Tree.branch (152 : Fin 175) _ = Tree.branch (152 : Fin 175) _
  apply congrArg (Tree.branch (152 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0174
  · rfl

def B0059 : Block := .branch 132 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 680564734158789576983806565237712248840, 1393799234013192623494581653220955196063760, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), Tip0057_0060, (.leaf 5 (Common.fact 329).pointIds 329), B0173]
theorem treeEq0059 : B0059.tree = HexagonCover.NBand.M8500_8700.SplitData.node0059 := by
  change Tree.branch (132 : Fin 175) _ = Tree.branch (132 : Fin 175) _
  apply congrArg (Tree.branch (132 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0173

def B0058 : Block := .branch 129 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 664614314805107993509253904315998216, 1393799234013192623494581653220955196063760, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), (.leaf 2 (Common.fact 322).pointIds 322), B0059, Tip0057_0180, (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 6 (Common.fact 324).pointIds 324)]
theorem treeEq0058 : B0058.tree = HexagonCover.NBand.M8500_8700.SplitData.node0058 := by
  change Tree.branch (129 : Fin 175) _ = Tree.branch (129 : Fin 175) _
  apply congrArg (Tree.branch (129 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0059
  · rfl
  · rfl
  · rfl

def B0198 : Block := .branch 170 ![36346078628713813621116163871211905, 309485009821345618480596482, 130601767450242908029982724, 664614314805107993509253904315998216, 649037107316853453566312041250832, 748294569604938316490434009030332976692744499363872, 11193973935983048381230849815516046371061824] ![(.leaf 0 (Common.fact 497).pointIds 497), (.leaf 1 (Common.fact 505).pointIds 505), (.leaf 2 (Common.fact 487).pointIds 487), (.leaf 3 (Common.fact 641).pointIds 641), (.leaf 4 (Common.fact 642).pointIds 642), (.leaf 5 (Common.fact 416).pointIds 416), (.leaf 6 (Common.fact 643).pointIds 643)]
theorem treeEq0198 : B0198.tree = HexagonCover.NBand.M8500_8700.SplitData.node0198 := by
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

def B0197 : Block := .branch 169 ![36346078628713813621116163871211905, 309485009821345618480596482, 130601767450242908029982724, 664614314805107993509253904315998216, 649037107316853453566312041250832, 5731291516022370147374679596070628907037360160, 3367299783604374259524338235809165892803314950078528] ![(.leaf 0 (Common.fact 499).pointIds 499), (.leaf 1 (Common.fact 506).pointIds 506), (.leaf 2 (Common.fact 490).pointIds 490), (.leaf 3 (Common.fact 638).pointIds 638), (.leaf 4 (Common.fact 639).pointIds 639), B0198, (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq0197 : B0197.tree = HexagonCover.NBand.M8500_8700.SplitData.node0197 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0198
  · rfl

def B0196 : Block := .branch 171 ![36346078628713813621116163871211905, 309485009821345618480596482, 130601767450242908029982724, 5986310706507379017576607879913888757764604012027912, 649037107316853453566312041250832, 5731291516022370147374679596070628907037360160, 374144430350685083043191698406218268547965102063680] ![(.leaf 0 (Common.fact 496).pointIds 496), (.leaf 1 (Common.fact 504).pointIds 504), (.leaf 2 (Common.fact 478).pointIds 478), (.leaf 3 (Common.fact 636).pointIds 636), (.leaf 4 (Common.fact 637).pointIds 637), (.leaf 5 (Common.fact 430).pointIds 430), B0197]
theorem treeEq0196 : B0196.tree = HexagonCover.NBand.M8500_8700.SplitData.node0196 := by
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
  · exact treeEq0197

def B0195 : Block := .branch 172 ![36346078628713813621116163871211905, 309485009821345618480596482, 130601767450242908029982724, 664614314805107993509253904315998216, 649037107316853453566312041250832, 5731291516022370147374679596070628907037360160, 374144430350685083043191698406218268547965102063680] ![(.leaf 0 (Common.fact 494).pointIds 494), (.leaf 1 (Common.fact 502).pointIds 502), (.leaf 2 (Common.fact 480).pointIds 480), B0196, (.leaf 4 (Common.fact 634).pointIds 634), (.leaf 5 (Common.fact 432).pointIds 432), (.leaf 6 (Common.fact 635).pointIds 635)]
theorem treeEq0195 : B0195.tree = HexagonCover.NBand.M8500_8700.SplitData.node0195 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0196
  · rfl
  · rfl
  · rfl

def B0194 : Block := .branch 168 ![36346078628713813621116163871211905, 309485009821345618480596482, 130601767450242908029982724, 664614314805107993509253904315998216, 649037107316853453566312041250832, 5731291516022370147374679596070628907037360160, 11193973935983048381230849815516046371061824] ![(.leaf 0 (Common.fact 493).pointIds 493), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 477).pointIds 477), (.leaf 3 (Common.fact 632).pointIds 632), (.leaf 4 (Common.fact 633).pointIds 633), (.leaf 5 (Common.fact 405).pointIds 405), B0195]
theorem treeEq0194 : B0194.tree = HexagonCover.NBand.M8500_8700.SplitData.node0194 := by
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
  · exact treeEq0195

def B0193 : Block := .branch 144 ![36346078628713813621116163871211905, 309485009821345618480596482, 130601767450242908029982724, 664614314805107993509253904315998216, 649037107316853453566312041250832, 5708990770823839524233143877797980545531379744, 11193973935983048381230849815516046371061824] ![(.leaf 0 (Common.fact 340).pointIds 340), (.leaf 1 (Common.fact 341).pointIds 341), (.leaf 2 (Common.fact 342).pointIds 342), (.leaf 3 (Common.fact 343).pointIds 343), (.leaf 4 (Common.fact 344).pointIds 344), B0194, (.leaf 6 (Common.fact 631).pointIds 631)]
theorem treeEq0193 : B0193.tree = HexagonCover.NBand.M8500_8700.SplitData.node0193 := by
  change Tree.branch (144 : Fin 175) _ = Tree.branch (144 : Fin 175) _
  apply congrArg (Tree.branch (144 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0194
  · rfl

def B0192 : Block := .branch 152 ![36346078628713813621116163871211905, 309485009821345618480596482, 130601767450242908029982724, 664614314805107993509253904315998216, 1393796575557201053662835845606834635374608, 393248, 11193973935983048381230849815516046371061824] ![(.leaf 0 (Common.fact 354).pointIds 354), (.leaf 1 (Common.fact 355).pointIds 355), (.leaf 2 (Common.fact 356).pointIds 356), (.leaf 3 (Common.fact 357).pointIds 357), (.leaf 4 (Common.fact 358).pointIds 358), B0193, (.leaf 6 (Common.fact 630).pointIds 630)]
theorem treeEq0192 : B0192.tree = HexagonCover.NBand.M8500_8700.SplitData.node0192 := by
  change Tree.branch (152 : Fin 175) _ = Tree.branch (152 : Fin 175) _
  apply congrArg (Tree.branch (152 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0193
  · rfl

def B0057 : Block := .branch 121 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 664614314805107993509253904315998216, 1393796575557201053662835845606834635374608, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 315).pointIds 315), (.leaf 1 (Common.fact 316).pointIds 316), (.leaf 2 (Common.fact 317).pointIds 317), (.leaf 3 (Common.fact 318).pointIds 318), B0058, (.leaf 5 (Common.fact 319).pointIds 319), B0192]
theorem treeEq0057 : B0057.tree = HexagonCover.NBand.M8500_8700.SplitData.node0057 := by
  change Tree.branch (121 : Fin 175) _ = Tree.branch (121 : Fin 175) _
  apply congrArg (Tree.branch (121 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0058
  · rfl
  · exact treeEq0192

theorem accepted0057 : B0057.accepted = true := by decide +kernel
theorem checked0057 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node0057 (maskNeeds ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 664614314805107993509253904315998216, 1393796575557201053662835845606834635374608, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq0057]
  exact B0057.sound accepted0057
#print axioms checked0057

end HexagonCover.NBand.M8500_8700.SplitTree.Run0001
