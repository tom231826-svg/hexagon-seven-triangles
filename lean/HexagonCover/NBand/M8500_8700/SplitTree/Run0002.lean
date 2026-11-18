import HexagonCover.NBand.M8500_8700.SplitData
import HexagonCover.NBand.M8500_8700.SplitTree.Run0001
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8500_8700.SplitTree.Run0002
open OwnerTree HexagonCover.NBand.M8500_8700

abbrev Block := Chunk (n := 175) (Certificate := Fin 1173) (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck

def Tip0055_0057 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node0057 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 664614314805107993509253904315998216, 1393796575557201053662835845606834635374608, 393248, 11226638384751466903891587970215375558672448] HexagonCover.NBand.M8500_8700.SplitTree.Run0001.checked0057
def B0210 : Block := .branch 170 ![36346078628713813621116163871211905, 309485009821345618480596482, 130601767450242908029982724, 5846006549323611672814739330865132078623730196488, 665263034999774789905469842181423120, 982134831577882783403023582264938259837693706240032, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 497).pointIds 497), (.leaf 1 (Common.fact 505).pointIds 505), (.leaf 2 (Common.fact 487).pointIds 487), (.leaf 3 (Common.fact 656).pointIds 656), (.leaf 4 (Common.fact 657).pointIds 657), (.leaf 5 (Common.fact 562).pointIds 562), (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq0210 : B0210.tree = HexagonCover.NBand.M8500_8700.SplitData.node0210 := by
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

def B0209 : Block := .branch 169 ![36346078628713813621116163871211905, 309485009821345618480596482, 130601767450242908029982724, 5846006549323611672814739330865132078623730196488, 665263034999774789905469842181423120, 233845993264460489282736947914201353773856244236320, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 499).pointIds 499), (.leaf 1 (Common.fact 506).pointIds 506), (.leaf 2 (Common.fact 490).pointIds 490), (.leaf 3 (Common.fact 654).pointIds 654), (.leaf 4 (Common.fact 655).pointIds 655), B0210, (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq0209 : B0209.tree = HexagonCover.NBand.M8500_8700.SplitData.node0209 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0210
  · rfl

def B0208 : Block := .branch 87 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 5846006549323611672814739330865132078623730196488, 665263034999774789905469842181423120, 233845993264460489282736947914201353773856244236320, 385836443449329647932829607236202725091092001718336] ![(.leaf 0 (Common.fact 378).pointIds 378), (.leaf 1 (Common.fact 379).pointIds 379), B0209, (.leaf 3 (Common.fact 653).pointIds 653), (.leaf 4 (Common.fact 381).pointIds 381), (.leaf 5 (Common.fact 382).pointIds 382), (.leaf 6 (Common.fact 557).pointIds 557)]
theorem treeEq0208 : B0208.tree = HexagonCover.NBand.M8500_8700.SplitData.node0208 := by
  change Tree.branch (87 : Fin 175) _ = Tree.branch (87 : Fin 175) _
  apply congrArg (Tree.branch (87 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0209
  · rfl
  · rfl
  · rfl
  · rfl

def B0207 : Block := .branch 171 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 5992156713056701964635107814136760380589323426226184, 665263034999774789905469842181423120, 233845993264460489282736947914201353773856244236320, 385836443449329647932829607236202725091092001718336] ![(.leaf 0 (Common.fact 496).pointIds 496), (.leaf 1 (Common.fact 504).pointIds 504), (.leaf 2 (Common.fact 478).pointIds 478), (.leaf 3 (Common.fact 651).pointIds 651), (.leaf 4 (Common.fact 652).pointIds 652), (.leaf 5 (Common.fact 555).pointIds 555), B0208]
theorem treeEq0207 : B0207.tree = HexagonCover.NBand.M8500_8700.SplitData.node0207 := by
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
  · exact treeEq0208

def B0206 : Block := .branch 172 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 5846006549323611672814739330865132078623730196488, 665263034999774789905469842181423120, 233845993264460489282736947914201353773856244236320, 385836443449329647932829607236202725091092001718336] ![(.leaf 0 (Common.fact 494).pointIds 494), (.leaf 1 (Common.fact 502).pointIds 502), (.leaf 2 (Common.fact 480).pointIds 480), B0207, (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 552).pointIds 552), (.leaf 6 (Common.fact 471).pointIds 471)]
theorem treeEq0206 : B0206.tree = HexagonCover.NBand.M8500_8700.SplitData.node0206 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0207
  · rfl
  · rfl
  · rfl

def B0205 : Block := .branch 168 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 5846006549323611672814739330865132078623730196488, 665263034999774789905469842181423120, 233845993264460489282736947914201353773856244236320, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 493).pointIds 493), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 477).pointIds 477), (.leaf 3 (Common.fact 648).pointIds 648), (.leaf 4 (Common.fact 649).pointIds 649), (.leaf 5 (Common.fact 550).pointIds 550), B0206]
theorem treeEq0205 : B0205.tree = HexagonCover.NBand.M8500_8700.SplitData.node0205 := by
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
  · exact treeEq0206

def B0204 : Block := .branch 162 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 24584, 665263034999774789905469842181423120, 233845993264460489282736947914201353773856244236320, 11692024325285608097096382553318234372623019016256] ![(.leaf 0 (Common.fact 373).pointIds 373), (.leaf 1 (Common.fact 374).pointIds 374), (.leaf 2 (Common.fact 375).pointIds 375), B0205, (.leaf 4 (Common.fact 647).pointIds 647), (.leaf 5 (Common.fact 376).pointIds 376), (.leaf 6 (Common.fact 377).pointIds 377)]
theorem treeEq0204 : B0204.tree = HexagonCover.NBand.M8500_8700.SplitData.node0204 := by
  change Tree.branch (162 : Fin 175) _ = Tree.branch (162 : Fin 175) _
  apply congrArg (Tree.branch (162 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0205
  · rfl
  · rfl
  · rfl

def B0203 : Block := .branch 144 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 24584, 665263034999774789905469842181423120, 233845970963715290752113806378483081125494738255904, 11692024325285608097096382553318234372623019016256] ![(.leaf 0 (Common.fact 340).pointIds 340), (.leaf 1 (Common.fact 341).pointIds 341), (.leaf 2 (Common.fact 342).pointIds 342), (.leaf 3 (Common.fact 343).pointIds 343), (.leaf 4 (Common.fact 344).pointIds 344), B0204, (.leaf 6 (Common.fact 590).pointIds 590)]
theorem treeEq0203 : B0203.tree = HexagonCover.NBand.M8500_8700.SplitData.node0203 := by
  change Tree.branch (144 : Fin 175) _ = Tree.branch (144 : Fin 175) _
  apply congrArg (Tree.branch (144 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0204
  · rfl

def B0202 : Block := .branch 152 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 24584, 1393797240171198946120772297510364775546896, 233840261972944466912589573234605283144949207269408, 11692024325285608097096382553318234372623019016256] ![(.leaf 0 (Common.fact 354).pointIds 354), (.leaf 1 (Common.fact 355).pointIds 355), (.leaf 2 (Common.fact 356).pointIds 356), (.leaf 3 (Common.fact 357).pointIds 357), (.leaf 4 (Common.fact 358).pointIds 358), B0203, (.leaf 6 (Common.fact 546).pointIds 546)]
theorem treeEq0202 : B0202.tree = HexagonCover.NBand.M8500_8700.SplitData.node0202 := by
  change Tree.branch (152 : Fin 175) _ = Tree.branch (152 : Fin 175) _
  apply congrArg (Tree.branch (152 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0203
  · rfl

def B0201 : Block := .branch 163 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 24584, 1393797240171198946120772297510364775546896, 233840261972944466912589573234605283144949207269408, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 387).pointIds 387), B0202]
theorem treeEq0201 : B0201.tree = HexagonCover.NBand.M8500_8700.SplitData.node0201 := by
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
  · exact treeEq0202

def B0200 : Block := .branch 165 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 24584, 1393797240171198946120772297510364775546896, 187072209578355573530071658587684226515959365894176, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 645).pointIds 645), B0201, (.leaf 0 [] 0)]
theorem treeEq0200 : B0200.tree = HexagonCover.NBand.M8500_8700.SplitData.node0200 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0201
  · rfl

def B0199 : Block := .branch 167 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 24584, 1393797240171198946120772297510364775546896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 644).pointIds 644), B0200, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq0199 : B0199.tree = HexagonCover.NBand.M8500_8700.SplitData.node0199 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0200
  · rfl

def B0056 : Block := .branch 119 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 316912650057057350374175825928, 1393796575557201053662835845606834635374608, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 310).pointIds 310), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), Tip0055_0057, B0199, (.leaf 5 (Common.fact 313).pointIds 313), (.leaf 6 (Common.fact 314).pointIds 314)]
theorem treeEq0056 : B0056.tree = HexagonCover.NBand.M8500_8700.SplitData.node0056 := by
  change Tree.branch (119 : Fin 175) _ = Tree.branch (119 : Fin 175) _
  apply congrArg (Tree.branch (119 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0199
  · rfl
  · rfl

def B0214 : Block := .branch 172 ![15576891194574503106994178554331521, 309485009821345618480596482, 130601767450242908029982724, 2993155353254369741214988414329874373470213384462344, 11692013098647223345629478661730264157247460442128, 393248, 11193971298296244245538414522023911127253056] ![(.leaf 0 (Common.fact 663).pointIds 663), (.leaf 1 (Common.fact 502).pointIds 502), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 664).pointIds 664), (.leaf 4 (Common.fact 665).pointIds 665), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 666).pointIds 666)]
theorem treeEq0214 : B0214.tree = HexagonCover.NBand.M8500_8700.SplitData.node0214 := by
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

def B0213 : Block := .branch 171 ![15576891194574503106994178554331521, 309485009821345618480596482, 130601767450242908029982724, 680564733841876926926749214863536447496, 11692013098647223345629478661730264157247460442128, 393248, 11193971298296244245538414522023911127253056] ![(.leaf 0 (Common.fact 660).pointIds 660), (.leaf 1 (Common.fact 504).pointIds 504), (.leaf 2 (Common.fact 478).pointIds 478), B0214, (.leaf 4 (Common.fact 661).pointIds 661), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq0213 : B0213.tree = HexagonCover.NBand.M8500_8700.SplitData.node0213 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0214
  · rfl
  · rfl
  · rfl

def B0212 : Block := .branch 129 ![15576891194574503106994178554331521, 309485009821345618480596482, 130601767450242908029982724, 24584, 11692013098647223345629478661730264157247460442128, 393248, 11226638405520654338030898484337360875552832] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), (.leaf 2 (Common.fact 322).pointIds 322), B0213, (.leaf 4 (Common.fact 659).pointIds 659), (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 6 (Common.fact 324).pointIds 324)]
theorem treeEq0212 : B0212.tree = HexagonCover.NBand.M8500_8700.SplitData.node0212 := by
  change Tree.branch (129 : Fin 175) _ = Tree.branch (129 : Fin 175) _
  apply congrArg (Tree.branch (129 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0213
  · rfl
  · rfl
  · rfl

def B0211 : Block := .branch 163 ![15576891194574503106994178554331521, 309485009821345618480596482, 130601767450242908029982724, 24584, 98320, 393248, 11226638405520654338030898484337360875552832] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), B0212, (.leaf 5 (Common.fact 387).pointIds 387), (.leaf 6 (Common.fact 658).pointIds 658)]
theorem treeEq0211 : B0211.tree = HexagonCover.NBand.M8500_8700.SplitData.node0211 := by
  change Tree.branch (163 : Fin 175) _ = Tree.branch (163 : Fin 175) _
  apply congrArg (Tree.branch (163 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0212
  · rfl
  · rfl

def B0055 : Block := .branch 114 ![15576891194574503106994178554331521, 309636125548797447127434754, 130601767450242908029982724, 316912650057057350374175825928, 1393796575557201053662835845606834635374608, 393248, 11226638384751466903891587970215375558672448] ![B0056, (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 308).pointIds 308), (.leaf 5 (Common.fact 309).pointIds 309), B0211]
theorem treeEq0055 : B0055.tree = HexagonCover.NBand.M8500_8700.SplitData.node0055 := by
  change Tree.branch (114 : Fin 175) _ = Tree.branch (114 : Fin 175) _
  apply congrArg (Tree.branch (114 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0056
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0211

theorem accepted0055 : B0055.accepted = true := by decide +kernel
theorem checked0055 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node0055 (maskNeeds ![15576891194574503106994178554331521, 309636125548797447127434754, 130601767450242908029982724, 316912650057057350374175825928, 1393796575557201053662835845606834635374608, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq0055]
  exact B0055.sound accepted0055
#print axioms checked0055

def B0232 : Block := .branch 169 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 324835466308483784133530196402184, 649037107316853453566312041250832, 1496577676626844588240573268701473812127674924400672, 3367299783604329065772481548669487163363265418362944] ![(.leaf 0 (Common.fact 682).pointIds 682), (.leaf 1 (Common.fact 506).pointIds 506), (.leaf 2 (Common.fact 490).pointIds 490), (.leaf 3 (Common.fact 675).pointIds 675), (.leaf 4 (Common.fact 639).pointIds 639), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 444).pointIds 444)]
theorem treeEq0232 : B0232.tree = HexagonCover.NBand.M8500_8700.SplitData.node0232 := by
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

def B0231 : Block := .branch 170 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 324835466308483784133530196402184, 649037107316853453566312041250832, 393248, 3367299783604329065772481548669487163363265418362944] ![(.leaf 0 (Common.fact 681).pointIds 681), (.leaf 1 (Common.fact 505).pointIds 505), (.leaf 2 (Common.fact 487).pointIds 487), (.leaf 3 (Common.fact 672).pointIds 672), (.leaf 4 (Common.fact 642).pointIds 642), B0232, (.leaf 6 (Common.fact 440).pointIds 440)]
theorem treeEq0231 : B0231.tree = HexagonCover.NBand.M8500_8700.SplitData.node0231 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0232
  · rfl

def B0230 : Block := .branch 171 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 5986310706855827497014169527700874630654360540962824, 649037107316853453566312041250832, 393248, 374144430350639889291335011266539539107915570348096] ![(.leaf 0 (Common.fact 680).pointIds 680), (.leaf 1 (Common.fact 504).pointIds 504), (.leaf 2 (Common.fact 478).pointIds 478), (.leaf 3 (Common.fact 578).pointIds 578), (.leaf 4 (Common.fact 637).pointIds 637), (.leaf 5 (Common.fact 566).pointIds 566), B0231]
theorem treeEq0230 : B0230.tree = HexagonCover.NBand.M8500_8700.SplitData.node0230 := by
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
  · exact treeEq0231

def B0229 : Block := .branch 172 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 348449144051876452894979382143660844933128, 649037107316853453566312041250832, 393248, 374144430350639889291335011266539539107915570348096] ![(.leaf 0 (Common.fact 679).pointIds 679), (.leaf 1 (Common.fact 502).pointIds 502), (.leaf 2 (Common.fact 480).pointIds 480), B0230, (.leaf 4 (Common.fact 634).pointIds 634), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 452).pointIds 452)]
theorem treeEq0229 : B0229.tree = HexagonCover.NBand.M8500_8700.SplitData.node0229 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0230
  · rfl
  · rfl
  · rfl

def B0228 : Block := .branch 168 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 348449144051876452894979382143660844933128, 649037107316853453566312041250832, 22300745198530623141535718272648361506373664, 11193928742231191694091171086075996839346240] ![(.leaf 0 (Common.fact 677).pointIds 677), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 477).pointIds 477), (.leaf 3 (Common.fact 678).pointIds 678), (.leaf 4 (Common.fact 633).pointIds 633), (.leaf 5 (Common.fact 517).pointIds 517), B0229]
theorem treeEq0228 : B0228.tree = HexagonCover.NBand.M8500_8700.SplitData.node0228 := by
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
  · exact treeEq0229

def B0234 : Block := .branch 171 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 5986310706855827496689650974042447903871204520386568, 649037107316853453566312041250832, 393248, 33451160338284096688146337959329517314506816] ![(.leaf 0 (Common.fact 680).pointIds 680), (.leaf 1 (Common.fact 504).pointIds 504), (.leaf 2 (Common.fact 478).pointIds 478), (.leaf 3 (Common.fact 578).pointIds 578), (.leaf 4 (Common.fact 637).pointIds 637), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 684).pointIds 684)]
theorem treeEq0234 : B0234.tree = HexagonCover.NBand.M8500_8700.SplitData.node0234 := by
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

def B0233 : Block := .branch 172 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 348449143727357899236552655360504824356872, 649037107316853453566312041250832, 393248, 33451160338284096688146337959329517314506816] ![(.leaf 0 (Common.fact 679).pointIds 679), (.leaf 1 (Common.fact 502).pointIds 502), (.leaf 2 (Common.fact 480).pointIds 480), B0234, (.leaf 4 (Common.fact 634).pointIds 634), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 683).pointIds 683)]
theorem treeEq0233 : B0233.tree = HexagonCover.NBand.M8500_8700.SplitData.node0233 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0234
  · rfl
  · rfl
  · rfl

def B0227 : Block := .branch 144 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 348449144051876452894979382143660844933128, 649037107316853453566312041250832, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 340).pointIds 340), (.leaf 1 (Common.fact 341).pointIds 341), (.leaf 2 (Common.fact 342).pointIds 342), (.leaf 3 (Common.fact 343).pointIds 343), (.leaf 4 (Common.fact 344).pointIds 344), B0228, B0233]
theorem treeEq0227 : B0227.tree = HexagonCover.NBand.M8500_8700.SplitData.node0227 := by
  change Tree.branch (144 : Fin 175) _ = Tree.branch (144 : Fin 175) _
  apply congrArg (Tree.branch (144 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0228
  · exact treeEq0233

def B0240 : Block := .branch 169 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 324835466308483784133530196402184, 649037107316853453566312041250832, 1496577676626844588240573268701473812127674924400672, 3367299789179515365405137334053416731525355794858048] ![(.leaf 0 (Common.fact 682).pointIds 682), (.leaf 1 (Common.fact 506).pointIds 506), (.leaf 2 (Common.fact 490).pointIds 490), (.leaf 3 (Common.fact 675).pointIds 675), (.leaf 4 (Common.fact 639).pointIds 639), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 586).pointIds 586)]
theorem treeEq0240 : B0240.tree = HexagonCover.NBand.M8500_8700.SplitData.node0240 := by
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

def B0239 : Block := .branch 170 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 324835466308483784133530196402184, 649037107316853453566312041250832, 393248, 3367299789179515365405137334053416731525355794858048] ![(.leaf 0 (Common.fact 681).pointIds 681), (.leaf 1 (Common.fact 505).pointIds 505), (.leaf 2 (Common.fact 487).pointIds 487), (.leaf 3 (Common.fact 672).pointIds 672), (.leaf 4 (Common.fact 642).pointIds 642), B0240, (.leaf 6 (Common.fact 583).pointIds 583)]
theorem treeEq0239 : B0239.tree = HexagonCover.NBand.M8500_8700.SplitData.node0239 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0240
  · rfl

def B0238 : Block := .branch 171 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 5986310706855827497014169527700874630654360540962824, 649037107316853453566312041250832, 393248, 374144435925826188923990796650469107270005946843200] ![(.leaf 0 (Common.fact 680).pointIds 680), (.leaf 1 (Common.fact 504).pointIds 504), (.leaf 2 (Common.fact 478).pointIds 478), (.leaf 3 (Common.fact 578).pointIds 578), (.leaf 4 (Common.fact 637).pointIds 637), (.leaf 5 (Common.fact 566).pointIds 566), B0239]
theorem treeEq0238 : B0238.tree = HexagonCover.NBand.M8500_8700.SplitData.node0238 := by
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
  · exact treeEq0239

def B0237 : Block := .branch 172 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 348449144051876452894979382143660844933128, 649037107316853453566312041250832, 393248, 374144435925826188923990796650469107270005946843200] ![(.leaf 0 (Common.fact 679).pointIds 679), (.leaf 1 (Common.fact 502).pointIds 502), (.leaf 2 (Common.fact 480).pointIds 480), B0238, (.leaf 4 (Common.fact 634).pointIds 634), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 577).pointIds 577)]
theorem treeEq0237 : B0237.tree = HexagonCover.NBand.M8500_8700.SplitData.node0237 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0238
  · rfl
  · rfl
  · rfl

def B0236 : Block := .branch 168 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 348449144051876452894979382143660844933128, 649037107316853453566312041250832, 5708990770823839524233143877797980545531379744, 16769115041863847479475100654238087215841344] ![(.leaf 0 (Common.fact 677).pointIds 677), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 477).pointIds 477), (.leaf 3 (Common.fact 678).pointIds 678), (.leaf 4 (Common.fact 633).pointIds 633), (.leaf 5 (Common.fact 574).pointIds 574), B0237]
theorem treeEq0236 : B0236.tree = HexagonCover.NBand.M8500_8700.SplitData.node0236 := by
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
  · exact treeEq0237

def B0235 : Block := .branch 152 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 348449144051876452894979382143660844933128, 1393796575557201053662835845606834635374608, 393248, 16769157582352009455317861204594512516087872] ![(.leaf 0 (Common.fact 354).pointIds 354), (.leaf 1 (Common.fact 355).pointIds 355), (.leaf 2 (Common.fact 356).pointIds 356), (.leaf 3 (Common.fact 357).pointIds 357), (.leaf 4 (Common.fact 358).pointIds 358), B0236, (.leaf 6 (Common.fact 685).pointIds 685)]
theorem treeEq0235 : B0235.tree = HexagonCover.NBand.M8500_8700.SplitData.node0235 := by
  change Tree.branch (152 : Fin 175) _ = Tree.branch (152 : Fin 175) _
  apply congrArg (Tree.branch (152 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0236
  · rfl

def B0226 : Block := .branch 142 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 348449144051876452894979382143660844933128, 1393796575557201053662835845606834635374608, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), B0227, (.leaf 5 (Common.fact 339).pointIds 339), B0235]
theorem treeEq0226 : B0226.tree = HexagonCover.NBand.M8500_8700.SplitData.node0226 := by
  change Tree.branch (142 : Fin 175) _ = Tree.branch (142 : Fin 175) _
  apply congrArg (Tree.branch (142 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0227
  · rfl
  · exact treeEq0235

theorem accepted0226 : B0226.accepted = true := by decide +kernel
theorem checked0226 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node0226 (maskNeeds ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 348449144051876452894979382143660844933128, 1393796575557201053662835845606834635374608, 393248, 11193971282719353669933931636432422139592768]) := by
  rw [← treeEq0226]
  exact B0226.sound accepted0226
#print axioms checked0226

def Tip0223_0226 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node0226 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 348449144051876452894979382143660844933128, 1393796575557201053662835845606834635374608, 393248, 11193971282719353669933931636432422139592768] checked0226
def B0245 : Block := .branch 169 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 324835466308483784133530196402184, 649037107316853453566312041250832, 1730417938599789055153162841936079095272624131276832, 11692024292618506064983148595661900589669599936576] ![(.leaf 0 (Common.fact 682).pointIds 682), (.leaf 1 (Common.fact 506).pointIds 506), (.leaf 2 (Common.fact 490).pointIds 490), (.leaf 3 (Common.fact 675).pointIds 675), (.leaf 4 (Common.fact 639).pointIds 639), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 688).pointIds 688)]
theorem treeEq0245 : B0245.tree = HexagonCover.NBand.M8500_8700.SplitData.node0245 := by
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

def B0244 : Block := .branch 170 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 324835466308483784133530196402184, 649037107316853453566312041250832, 233840261972944466912589573234605283144949207269408, 11692024292618506064983148595661900589669599936576] ![(.leaf 0 (Common.fact 681).pointIds 681), (.leaf 1 (Common.fact 505).pointIds 505), (.leaf 2 (Common.fact 487).pointIds 487), (.leaf 3 (Common.fact 672).pointIds 672), (.leaf 4 (Common.fact 642).pointIds 642), B0245, (.leaf 6 (Common.fact 686).pointIds 686)]
theorem treeEq0244 : B0244.tree = HexagonCover.NBand.M8500_8700.SplitData.node0244 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0245
  · rfl

def B0243 : Block := .branch 163 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 324835466308483784133530196402184, 353893662246813109318763045295350981165072, 233840261972944466912589573234605283144949207269408, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 589).pointIds 589), (.leaf 5 (Common.fact 387).pointIds 387), B0244]
theorem treeEq0243 : B0243.tree = HexagonCover.NBand.M8500_8700.SplitData.node0243 := by
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
  · exact treeEq0244

def B0242 : Block := .branch 165 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 324835466308483784133530196402184, 353893662246813109318763045295350981165072, 187072209578355573530071658587684226515959365894176, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 588).pointIds 588), B0243, (.leaf 0 [] 0)]
theorem treeEq0242 : B0242.tree = HexagonCover.NBand.M8500_8700.SplitData.node0242 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0243
  · rfl

def B0241 : Block := .branch 167 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 324835466308483784133530196402184, 353893662246813109318763045295350981165072, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 587).pointIds 587), B0242, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq0241 : B0241.tree = HexagonCover.NBand.M8500_8700.SplitData.node0241 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0242
  · rfl

def B0225 : Block := .branch 138 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 324835466308483784133530196402184, 1399241093427936069078249839325742926757904, 393248, 11226638389943763762426415598745871887892544] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), Tip0223_0226, B0241, (.leaf 5 (Common.fact 333).pointIds 333), (.leaf 6 (Common.fact 334).pointIds 334)]
theorem treeEq0225 : B0225.tree = HexagonCover.NBand.M8500_8700.SplitData.node0225 := by
  change Tree.branch (138 : Fin 175) _ = Tree.branch (138 : Fin 175) _
  apply congrArg (Tree.branch (138 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0241
  · rfl
  · rfl

def B0251 : Block := .branch 169 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 324835466308483784133530196402184, 649037107316853453566312041250832, 1496577676626844588240573268701473812127674924400672, 3367299783609773583643216564084901157082173709746240] ![(.leaf 0 (Common.fact 682).pointIds 682), (.leaf 1 (Common.fact 506).pointIds 506), (.leaf 2 (Common.fact 490).pointIds 490), (.leaf 3 (Common.fact 675).pointIds 675), (.leaf 4 (Common.fact 639).pointIds 639), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 615).pointIds 615)]
theorem treeEq0251 : B0251.tree = HexagonCover.NBand.M8500_8700.SplitData.node0251 := by
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

def B0250 : Block := .branch 170 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 324835466308483784133530196402184, 649037107316853453566312041250832, 393248, 3367299783609773583643216564084901157082173709746240] ![(.leaf 0 (Common.fact 681).pointIds 681), (.leaf 1 (Common.fact 505).pointIds 505), (.leaf 2 (Common.fact 487).pointIds 487), (.leaf 3 (Common.fact 672).pointIds 672), (.leaf 4 (Common.fact 642).pointIds 642), B0251, (.leaf 6 (Common.fact 612).pointIds 612)]
theorem treeEq0250 : B0250.tree = HexagonCover.NBand.M8500_8700.SplitData.node0250 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0251
  · rfl

def B0249 : Block := .branch 171 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 5986310706508058918020970418041305781859093428854792, 649037107316853453566312041250832, 393248, 374144430356084407162070026681953532826823861731392] ![(.leaf 0 (Common.fact 680).pointIds 680), (.leaf 1 (Common.fact 504).pointIds 504), (.leaf 2 (Common.fact 478).pointIds 478), (.leaf 3 (Common.fact 608).pointIds 608), (.leaf 4 (Common.fact 637).pointIds 637), (.leaf 5 (Common.fact 566).pointIds 566), B0250]
theorem treeEq0249 : B0249.tree = HexagonCover.NBand.M8500_8700.SplitData.node0249 := by
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
  · exact treeEq0250

def B0248 : Block := .branch 172 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 680565058677343235410533348393732825096, 649037107316853453566312041250832, 393248, 374144430356084407162070026681953532826823861731392] ![(.leaf 0 (Common.fact 679).pointIds 679), (.leaf 1 (Common.fact 502).pointIds 502), (.leaf 2 (Common.fact 480).pointIds 480), B0249, (.leaf 4 (Common.fact 634).pointIds 634), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 607).pointIds 607)]
theorem treeEq0248 : B0248.tree = HexagonCover.NBand.M8500_8700.SplitData.node0248 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0249
  · rfl
  · rfl
  · rfl

def B0247 : Block := .branch 168 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 680565058677343235410533348393732825096, 649037107316853453566312041250832, 5708990770823839524233143877797980545531379744, 11199373260101926709506585079794905130729536] ![(.leaf 0 (Common.fact 677).pointIds 677), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 477).pointIds 477), (.leaf 3 (Common.fact 678).pointIds 678), (.leaf 4 (Common.fact 633).pointIds 633), (.leaf 5 (Common.fact 574).pointIds 574), B0248]
theorem treeEq0247 : B0247.tree = HexagonCover.NBand.M8500_8700.SplitData.node0247 := by
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
  · exact treeEq0248

def B0246 : Block := .branch 152 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 680565058677343235410533348393732825096, 1393796575557201053662835845606834635374608, 393248, 11199415800590088685349345630151330430976064] ![(.leaf 0 (Common.fact 354).pointIds 354), (.leaf 1 (Common.fact 355).pointIds 355), (.leaf 2 (Common.fact 356).pointIds 356), (.leaf 3 (Common.fact 357).pointIds 357), (.leaf 4 (Common.fact 358).pointIds 358), B0247, (.leaf 6 (Common.fact 689).pointIds 689)]
theorem treeEq0246 : B0246.tree = HexagonCover.NBand.M8500_8700.SplitData.node0246 := by
  change Tree.branch (152 : Fin 175) _ = Tree.branch (152 : Fin 175) _
  apply congrArg (Tree.branch (152 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0247
  · rfl

def B0224 : Block := .branch 132 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 680565058677343235410533348393732825096, 1393796575557201053662835845606834635374608, 393248, 11226638389943763762426415598745871887892544] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B0225, (.leaf 5 (Common.fact 329).pointIds 329), B0246]
theorem treeEq0224 : B0224.tree = HexagonCover.NBand.M8500_8700.SplitData.node0224 := by
  change Tree.branch (132 : Fin 175) _ = Tree.branch (132 : Fin 175) _
  apply congrArg (Tree.branch (132 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0225
  · rfl
  · exact treeEq0246

def B0256 : Block := .branch 169 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 324835466308483784133530196402184, 649037107316853453566312041250832, 1730417938599789055153162841936079095272624131276832, 11692024292618506064983148595661900589669599936576] ![(.leaf 0 (Common.fact 682).pointIds 682), (.leaf 1 (Common.fact 506).pointIds 506), (.leaf 2 (Common.fact 490).pointIds 490), (.leaf 3 (Common.fact 675).pointIds 675), (.leaf 4 (Common.fact 639).pointIds 639), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 688).pointIds 688)]
theorem treeEq0256 : B0256.tree = HexagonCover.NBand.M8500_8700.SplitData.node0256 := by
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

def B0255 : Block := .branch 170 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 324835466308483784133530196402184, 649037107316853453566312041250832, 233840261972944466912589573234605283144949207269408, 11692024292618506064983148595661900589669599936576] ![(.leaf 0 (Common.fact 681).pointIds 681), (.leaf 1 (Common.fact 505).pointIds 505), (.leaf 2 (Common.fact 487).pointIds 487), (.leaf 3 (Common.fact 672).pointIds 672), (.leaf 4 (Common.fact 642).pointIds 642), B0256, (.leaf 6 (Common.fact 686).pointIds 686)]
theorem treeEq0255 : B0255.tree = HexagonCover.NBand.M8500_8700.SplitData.node0255 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0256
  · rfl

def B0254 : Block := .branch 163 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 324835466308483784133530196402184, 683223838870554075526010395296138362896, 233840261972944466912589573234605283144949207269408, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 618).pointIds 618), (.leaf 5 (Common.fact 387).pointIds 387), B0255]
theorem treeEq0254 : B0254.tree = HexagonCover.NBand.M8500_8700.SplitData.node0254 := by
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
  · exact treeEq0255

def B0253 : Block := .branch 165 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 324835466308483784133530196402184, 683223838870554075526010395296138362896, 187072209578355573530071658587684226515959365894176, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 617).pointIds 617), B0254, (.leaf 0 [] 0)]
theorem treeEq0253 : B0253.tree = HexagonCover.NBand.M8500_8700.SplitData.node0253 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0254
  · rfl

def B0252 : Block := .branch 167 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 324835466308483784133530196402184, 683223838870554075526010395296138362896, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 616).pointIds 616), B0253, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq0252 : B0252.tree = HexagonCover.NBand.M8500_8700.SplitData.node0252 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0253
  · rfl

def B0223 : Block := .branch 129 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 324835466308483784133530196402184, 1393799234013192623494581653220955196063760, 393248, 11226638389943763762426415598745871887892544] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), (.leaf 2 (Common.fact 322).pointIds 322), B0224, B0252, (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 6 (Common.fact 324).pointIds 324)]
theorem treeEq0223 : B0223.tree = HexagonCover.NBand.M8500_8700.SplitData.node0223 := by
  change Tree.branch (129 : Fin 175) _ = Tree.branch (129 : Fin 175) _
  apply congrArg (Tree.branch (129 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0224
  · exact treeEq0252
  · rfl
  · rfl

theorem accepted0223 : B0223.accepted = true := by decide +kernel
theorem checked0223 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node0223 (maskNeeds ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 324835466308483784133530196402184, 1393799234013192623494581653220955196063760, 393248, 11226638389943763762426415598745871887892544]) := by
  rw [← treeEq0223]
  exact B0223.sound accepted0223
#print axioms checked0223

def Tip0219_0223 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node0223 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 324835466308483784133530196402184, 1393799234013192623494581653220955196063760, 393248, 11226638389943763762426415598745871887892544] checked0223
def B0260 : Block := .branch 171 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 5986310706507379017576607879913888757764604012027912, 649037107316853453566312041250832, 393248, 748288849507353694807469898273653799753954862039104] ![(.leaf 0 (Common.fact 680).pointIds 680), (.leaf 1 (Common.fact 504).pointIds 504), (.leaf 2 (Common.fact 478).pointIds 478), (.leaf 3 (Common.fact 636).pointIds 636), (.leaf 4 (Common.fact 637).pointIds 637), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 692).pointIds 692)]
theorem treeEq0260 : B0260.tree = HexagonCover.NBand.M8500_8700.SplitData.node0260 := by
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

def B0259 : Block := .branch 172 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 664614314805107993509253904315998216, 649037107316853453566312041250832, 393248, 748288849507353694807469898273653799753954862039104] ![(.leaf 0 (Common.fact 679).pointIds 679), (.leaf 1 (Common.fact 502).pointIds 502), (.leaf 2 (Common.fact 480).pointIds 480), B0260, (.leaf 4 (Common.fact 634).pointIds 634), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 691).pointIds 691)]
theorem treeEq0259 : B0259.tree = HexagonCover.NBand.M8500_8700.SplitData.node0259 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0260
  · rfl
  · rfl
  · rfl

def B0258 : Block := .branch 169 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 664938833358766420236037060336574472, 649037107316853453566312041250832, 1496577676626844588240573268701473812127674924400672, 11193931400687183263922916893690117400035392] ![(.leaf 0 (Common.fact 682).pointIds 682), (.leaf 1 (Common.fact 506).pointIds 506), (.leaf 2 (Common.fact 490).pointIds 490), (.leaf 3 (Common.fact 675).pointIds 675), (.leaf 4 (Common.fact 639).pointIds 639), (.leaf 5 (Common.fact 443).pointIds 443), B0259]
theorem treeEq0258 : B0258.tree = HexagonCover.NBand.M8500_8700.SplitData.node0258 := by
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
  · exact treeEq0259

def B0257 : Block := .branch 170 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 664938833358766420236037060336574472, 649037107316853453566312041250832, 393248, 11193973941175345239765677444046542700281920] ![(.leaf 0 (Common.fact 681).pointIds 681), (.leaf 1 (Common.fact 505).pointIds 505), (.leaf 2 (Common.fact 487).pointIds 487), (.leaf 3 (Common.fact 672).pointIds 672), (.leaf 4 (Common.fact 642).pointIds 642), B0258, (.leaf 6 (Common.fact 690).pointIds 690)]
theorem treeEq0257 : B0257.tree = HexagonCover.NBand.M8500_8700.SplitData.node0257 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0258
  · rfl

def B0222 : Block := .branch 121 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 664938833358766420236037060336574472, 1393796575557201053662835845606834635374608, 393248, 11226638389943763762426415598745871887892544] ![(.leaf 0 (Common.fact 315).pointIds 315), (.leaf 1 (Common.fact 316).pointIds 316), (.leaf 2 (Common.fact 317).pointIds 317), (.leaf 3 (Common.fact 318).pointIds 318), Tip0219_0223, (.leaf 5 (Common.fact 319).pointIds 319), B0257]
theorem treeEq0222 : B0222.tree = HexagonCover.NBand.M8500_8700.SplitData.node0222 := by
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
  · exact treeEq0257

def B0265 : Block := .branch 169 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 324835466308483784133530196402184, 649037107316853453566312041250832, 1730417938599789055153162841936079095272624131276832, 11692024292618506064983148595661900589669599936576] ![(.leaf 0 (Common.fact 682).pointIds 682), (.leaf 1 (Common.fact 506).pointIds 506), (.leaf 2 (Common.fact 490).pointIds 490), (.leaf 3 (Common.fact 675).pointIds 675), (.leaf 4 (Common.fact 639).pointIds 639), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 688).pointIds 688)]
theorem treeEq0265 : B0265.tree = HexagonCover.NBand.M8500_8700.SplitData.node0265 := by
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

def B0264 : Block := .branch 170 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 324835466308483784133530196402184, 649037107316853453566312041250832, 233840261972944466912589573234605283144949207269408, 11692024292618506064983148595661900589669599936576] ![(.leaf 0 (Common.fact 681).pointIds 681), (.leaf 1 (Common.fact 505).pointIds 505), (.leaf 2 (Common.fact 487).pointIds 487), (.leaf 3 (Common.fact 672).pointIds 672), (.leaf 4 (Common.fact 642).pointIds 642), B0265, (.leaf 6 (Common.fact 686).pointIds 686)]
theorem treeEq0264 : B0264.tree = HexagonCover.NBand.M8500_8700.SplitData.node0264 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0265
  · rfl

def B0263 : Block := .branch 163 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 324835466308483784133530196402184, 665263034999774789905469842181423120, 233840261972944466912589573234605283144949207269408, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 387).pointIds 387), B0264]
theorem treeEq0263 : B0263.tree = HexagonCover.NBand.M8500_8700.SplitData.node0263 := by
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
  · exact treeEq0264

def B0262 : Block := .branch 165 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 324835466308483784133530196402184, 665263034999774789905469842181423120, 187072209578355573530071658587684226515959365894176, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 645).pointIds 645), B0263, (.leaf 0 [] 0)]
theorem treeEq0262 : B0262.tree = HexagonCover.NBand.M8500_8700.SplitData.node0262 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0263
  · rfl

def B0261 : Block := .branch 167 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 324835466308483784133530196402184, 665263034999774789905469842181423120, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 644).pointIds 644), B0262, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq0261 : B0261.tree = HexagonCover.NBand.M8500_8700.SplitData.node0261 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0262
  · rfl

def B0221 : Block := .branch 119 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 324835466308483784133530196402184, 1393796575557201053662835845606834635374608, 393248, 11226638389943763762426415598745871887892544] ![(.leaf 0 (Common.fact 310).pointIds 310), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), B0222, B0261, (.leaf 5 (Common.fact 313).pointIds 313), (.leaf 6 (Common.fact 314).pointIds 314)]
theorem treeEq0221 : B0221.tree = HexagonCover.NBand.M8500_8700.SplitData.node0221 := by
  change Tree.branch (119 : Fin 175) _ = Tree.branch (119 : Fin 175) _
  apply congrArg (Tree.branch (119 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0222
  · exact treeEq0261
  · rfl
  · rfl

def B0267 : Block := .branch 171 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 5986310706507378353287128541114379032644229892431880, 649037107316853453566312041250832, 393248, 11193971298296244245538414522023911127253056] ![(.leaf 0 (Common.fact 680).pointIds 680), (.leaf 1 (Common.fact 504).pointIds 504), (.leaf 2 (Common.fact 478).pointIds 478), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 637).pointIds 637), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq0267 : B0267.tree = HexagonCover.NBand.M8500_8700.SplitData.node0267 := by
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

def B0266 : Block := .branch 172 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 324835466308483784133530196402184, 649037107316853453566312041250832, 393248, 11193971298296244245538414522023911127253056] ![(.leaf 0 (Common.fact 679).pointIds 679), (.leaf 1 (Common.fact 502).pointIds 502), (.leaf 2 (Common.fact 480).pointIds 480), B0267, (.leaf 4 (Common.fact 634).pointIds 634), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 666).pointIds 666)]
theorem treeEq0266 : B0266.tree = HexagonCover.NBand.M8500_8700.SplitData.node0266 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0267
  · rfl
  · rfl
  · rfl

def B0220 : Block := .branch 114 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 324835466308483784133530196402184, 1393796575557201053662835845606834635374608, 393248, 11226638389943763762426415598745871887892544] ![B0221, (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 308).pointIds 308), (.leaf 5 (Common.fact 309).pointIds 309), B0266]
theorem treeEq0220 : B0220.tree = HexagonCover.NBand.M8500_8700.SplitData.node0220 := by
  change Tree.branch (114 : Fin 175) _ = Tree.branch (114 : Fin 175) _
  apply congrArg (Tree.branch (114 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0221
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0266

def B0271 : Block := .branch 169 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 324835466308483784133530196402184, 649037107316853453566312041250832, 1496577676626844588240573268701473812127674924400672, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 682).pointIds 682), (.leaf 1 (Common.fact 506).pointIds 506), (.leaf 2 (Common.fact 490).pointIds 490), (.leaf 3 (Common.fact 675).pointIds 675), (.leaf 4 (Common.fact 639).pointIds 639), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq0271 : B0271.tree = HexagonCover.NBand.M8500_8700.SplitData.node0271 := by
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

def B0270 : Block := .branch 170 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 324835466308483784133530196402184, 649037107316853453566312041250832, 393248, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 681).pointIds 681), (.leaf 1 (Common.fact 505).pointIds 505), (.leaf 2 (Common.fact 487).pointIds 487), (.leaf 3 (Common.fact 672).pointIds 672), (.leaf 4 (Common.fact 642).pointIds 642), B0271, (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq0270 : B0270.tree = HexagonCover.NBand.M8500_8700.SplitData.node0270 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0271
  · rfl

def B0269 : Block := .branch 171 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 5986310706507378353287128541114379032644229892431880, 649037107316853453566312041250832, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 680).pointIds 680), (.leaf 1 (Common.fact 504).pointIds 504), (.leaf 2 (Common.fact 478).pointIds 478), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 637).pointIds 637), (.leaf 5 (Common.fact 566).pointIds 566), B0270]
theorem treeEq0269 : B0269.tree = HexagonCover.NBand.M8500_8700.SplitData.node0269 := by
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
  · exact treeEq0270

def B0268 : Block := .branch 172 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 324835466308483784133530196402184, 649037107316853453566312041250832, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 679).pointIds 679), (.leaf 1 (Common.fact 502).pointIds 502), (.leaf 2 (Common.fact 480).pointIds 480), B0269, (.leaf 4 (Common.fact 634).pointIds 634), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq0268 : B0268.tree = HexagonCover.NBand.M8500_8700.SplitData.node0268 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0269
  · rfl
  · rfl
  · rfl

def B0219 : Block := .branch 113 ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 324835466308483784133530196402184, 1393796575557201053662835845606834635374608, 393248, 11226638389943763762426415598745871887892544] ![B0220, (.leaf 1 (Common.fact 300).pointIds 300), (.leaf 2 (Common.fact 301).pointIds 301), (.leaf 3 (Common.fact 302).pointIds 302), (.leaf 4 (Common.fact 303).pointIds 303), (.leaf 5 (Common.fact 304).pointIds 304), B0268]
theorem treeEq0219 : B0219.tree = HexagonCover.NBand.M8500_8700.SplitData.node0219 := by
  change Tree.branch (113 : Fin 175) _ = Tree.branch (113 : Fin 175) _
  apply congrArg (Tree.branch (113 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0220
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0268

theorem accepted0219 : B0219.accepted = true := by decide +kernel
theorem checked0219 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node0219 (maskNeeds ![1268269570248450804186269876609, 309485009821345618480596482, 130601767450242908029982724, 324835466308483784133530196402184, 1393796575557201053662835845606834635374608, 393248, 11226638389943763762426415598745871887892544]) := by
  rw [← treeEq0219]
  exact B0219.sound accepted0219
#print axioms checked0219

end HexagonCover.NBand.M8500_8700.SplitTree.Run0002
