import HexagonCover.NBand.M8500_8700.SplitData
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8500_8700.SplitTree.Run0032
open OwnerTree HexagonCover.NBand.M8500_8700

abbrev Block := Chunk (n := 175) (Certificate := Fin 1173) (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck

def B2359 : Block := .branch 169 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 3367299783604329065772481548669487163363265418362944] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 922).pointIds 922), (.leaf 2 (Common.fact 923).pointIds 923), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 444).pointIds 444)]
theorem treeEq2359 : B2359.tree = HexagonCover.NBand.M8500_8700.SplitData.node2359 := by
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

def B2358 : Block := .branch 170 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 3367299783604329065772481548669487163363265418362944] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 920).pointIds 920), (.leaf 2 (Common.fact 921).pointIds 921), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B2359, (.leaf 6 (Common.fact 440).pointIds 440)]
theorem treeEq2358 : B2358.tree = HexagonCover.NBand.M8500_8700.SplitData.node2358 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2359
  · rfl

def B2357 : Block := .branch 171 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 5986310706855827496689809430367476432546391608287240, 1329227995784915872903807060280442896, 393248, 374144430350639889291335011266539539107915570348096] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 578).pointIds 578), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B2358]
theorem treeEq2357 : B2357.tree = HexagonCover.NBand.M8500_8700.SplitData.node2357 := by
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
  · exact treeEq2358

def B2356 : Block := .branch 172 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 393248, 374144430350639889291335011266539539107915570348096] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 916).pointIds 916), (.leaf 2 (Common.fact 917).pointIds 917), B2357, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 452).pointIds 452)]
theorem treeEq2356 : B2356.tree = HexagonCover.NBand.M8500_8700.SplitData.node2356 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2357
  · rfl
  · rfl
  · rfl

def B2355 : Block := .branch 168 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 22300745198530623141535718272648361506373664, 11193928742231191694091171086075996839346240] ![(.leaf 0 (Common.fact 909).pointIds 909), (.leaf 1 (Common.fact 914).pointIds 914), (.leaf 2 (Common.fact 915).pointIds 915), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 517).pointIds 517), B2356]
theorem treeEq2355 : B2355.tree = HexagonCover.NBand.M8500_8700.SplitData.node2355 := by
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
  · exact treeEq2356

def B2361 : Block := .branch 171 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 5986310706855827496689650974042447903871204520386568, 1329227995784915872903807060280442896, 393248, 33451160333091799829611510330799020985286720] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 578).pointIds 578), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 567).pointIds 567)]
theorem treeEq2361 : B2361.tree = HexagonCover.NBand.M8500_8700.SplitData.node2361 := by
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

def B2360 : Block := .branch 172 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 348449143727357899236552655360504824356872, 1329227995784915872903807060280442896, 393248, 33451160333091799829611510330799020985286720] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 916).pointIds 916), (.leaf 2 (Common.fact 917).pointIds 917), B2361, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 570).pointIds 570)]
theorem treeEq2360 : B2360.tree = HexagonCover.NBand.M8500_8700.SplitData.node2360 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2361
  · rfl
  · rfl
  · rfl

def B2354 : Block := .branch 144 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 340).pointIds 340), (.leaf 1 (Common.fact 341).pointIds 341), (.leaf 2 (Common.fact 342).pointIds 342), (.leaf 3 (Common.fact 343).pointIds 343), (.leaf 4 (Common.fact 344).pointIds 344), B2355, B2360]
theorem treeEq2354 : B2354.tree = HexagonCover.NBand.M8500_8700.SplitData.node2354 := by
  change Tree.branch (144 : Fin 175) _ = Tree.branch (144 : Fin 175) _
  apply congrArg (Tree.branch (144 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2355
  · exact treeEq2360

def B2367 : Block := .branch 169 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 3367299789179515365405137334053416731525355794858048] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 922).pointIds 922), (.leaf 2 (Common.fact 923).pointIds 923), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 586).pointIds 586)]
theorem treeEq2367 : B2367.tree = HexagonCover.NBand.M8500_8700.SplitData.node2367 := by
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

def B2366 : Block := .branch 170 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 3367299789179515365405137334053416731525355794858048] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 920).pointIds 920), (.leaf 2 (Common.fact 921).pointIds 921), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B2367, (.leaf 6 (Common.fact 583).pointIds 583)]
theorem treeEq2366 : B2366.tree = HexagonCover.NBand.M8500_8700.SplitData.node2366 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2367
  · rfl

def B2365 : Block := .branch 171 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 5986310706855827496689809430367476432546391608287240, 1329227995784915872903807060280442896, 393248, 374144435925826188923990796650469107270005946843200] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 578).pointIds 578), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B2366]
theorem treeEq2365 : B2365.tree = HexagonCover.NBand.M8500_8700.SplitData.node2365 := by
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
  · exact treeEq2366

def B2364 : Block := .branch 172 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 393248, 374144435925826188923990796650469107270005946843200] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 916).pointIds 916), (.leaf 2 (Common.fact 917).pointIds 917), B2365, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 577).pointIds 577)]
theorem treeEq2364 : B2364.tree = HexagonCover.NBand.M8500_8700.SplitData.node2364 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2365
  · rfl
  · rfl
  · rfl

def B2363 : Block := .branch 168 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 5708990770823839524233143877797980545531379744, 16769115041863847479475100654238087215841344] ![(.leaf 0 (Common.fact 909).pointIds 909), (.leaf 1 (Common.fact 914).pointIds 914), (.leaf 2 (Common.fact 915).pointIds 915), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 574).pointIds 574), B2364]
theorem treeEq2363 : B2363.tree = HexagonCover.NBand.M8500_8700.SplitData.node2363 := by
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
  · exact treeEq2364

def B2362 : Block := .branch 152 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 16769157577159712596783033576064016186867776] ![(.leaf 0 (Common.fact 354).pointIds 354), (.leaf 1 (Common.fact 355).pointIds 355), (.leaf 2 (Common.fact 356).pointIds 356), (.leaf 3 (Common.fact 357).pointIds 357), (.leaf 4 (Common.fact 358).pointIds 358), B2363, (.leaf 6 (Common.fact 571).pointIds 571)]
theorem treeEq2362 : B2362.tree = HexagonCover.NBand.M8500_8700.SplitData.node2362 := by
  change Tree.branch (152 : Fin 175) _ = Tree.branch (152 : Fin 175) _
  apply congrArg (Tree.branch (152 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2363
  · rfl

def B2353 : Block := .branch 142 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), B2354, (.leaf 5 (Common.fact 339).pointIds 339), B2362]
theorem treeEq2353 : B2353.tree = HexagonCover.NBand.M8500_8700.SplitData.node2353 := by
  change Tree.branch (142 : Fin 175) _ = Tree.branch (142 : Fin 175) _
  apply congrArg (Tree.branch (142 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2354
  · rfl
  · exact treeEq2362

theorem accepted2353 : B2353.accepted = true := by decide +kernel
theorem checked2353 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node2353 (maskNeeds ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 11193971277527056811399104007901925810372672]) := by
  rw [← treeEq2353]
  exact B2353.sound accepted2353
#print axioms checked2353

def Tip2350_2353 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node2353 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 11193971277527056811399104007901925810372672] checked2353
def B2372 : Block := .branch 169 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 922).pointIds 922), (.leaf 2 (Common.fact 923).pointIds 923), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq2372 : B2372.tree = HexagonCover.NBand.M8500_8700.SplitData.node2372 := by
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

def B2371 : Block := .branch 170 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 920).pointIds 920), (.leaf 2 (Common.fact 921).pointIds 921), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B2372, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq2371 : B2371.tree = HexagonCover.NBand.M8500_8700.SplitData.node2371 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2372
  · rfl

def B2370 : Block := .branch 163 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 353894991474808894234635949102411261509648, 233840261972944466912589573234605283144949207269408, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 589).pointIds 589), (.leaf 5 (Common.fact 387).pointIds 387), B2371]
theorem treeEq2370 : B2370.tree = HexagonCover.NBand.M8500_8700.SplitData.node2370 := by
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
  · exact treeEq2371

def B2369 : Block := .branch 165 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 353894991474808894234635949102411261509648, 187072209578355573530071658587684226515959365894176, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 588).pointIds 588), B2370, (.leaf 0 [] 0)]
theorem treeEq2369 : B2369.tree = HexagonCover.NBand.M8500_8700.SplitData.node2369 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2370
  · rfl

def B2368 : Block := .branch 167 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 353894991474808894234635949102411261509648, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 587).pointIds 587), B2369, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq2368 : B2368.tree = HexagonCover.NBand.M8500_8700.SplitData.node2368 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2369
  · rfl

def B2352 : Block := .branch 138 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 475368975085586025561263726600, 1399242422655931853994122743132803207102480, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), Tip2350_2353, B2368, (.leaf 5 (Common.fact 333).pointIds 333), (.leaf 6 (Common.fact 334).pointIds 334)]
theorem treeEq2352 : B2352.tree = HexagonCover.NBand.M8500_8700.SplitData.node2352 := by
  change Tree.branch (138 : Fin 175) _ = Tree.branch (138 : Fin 175) _
  apply congrArg (Tree.branch (138 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2368
  · rfl
  · rfl

def B2378 : Block := .branch 169 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 3367299783609773583643216564084901157082173709746240] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 922).pointIds 922), (.leaf 2 (Common.fact 923).pointIds 923), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 615).pointIds 615)]
theorem treeEq2378 : B2378.tree = HexagonCover.NBand.M8500_8700.SplitData.node2378 := by
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

def B2377 : Block := .branch 170 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 3367299783609773583643216564084901157082173709746240] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 920).pointIds 920), (.leaf 2 (Common.fact 921).pointIds 921), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B2378, (.leaf 6 (Common.fact 612).pointIds 612)]
theorem treeEq2377 : B2377.tree = HexagonCover.NBand.M8500_8700.SplitData.node2377 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2378
  · rfl

def B2376 : Block := .branch 171 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 5986310706508058917696610320707907583751124496179208, 1329227995784915872903807060280442896, 393248, 374144430356084407162070026681953532826823861731392] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 608).pointIds 608), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B2377]
theorem treeEq2376 : B2376.tree = HexagonCover.NBand.M8500_8700.SplitData.node2376 := by
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
  · exact treeEq2377

def B2375 : Block := .branch 172 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 680564734317245902012335240424800149512, 1329227995784915872903807060280442896, 393248, 374144430356084407162070026681953532826823861731392] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 916).pointIds 916), (.leaf 2 (Common.fact 917).pointIds 917), B2376, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 607).pointIds 607)]
theorem treeEq2375 : B2375.tree = HexagonCover.NBand.M8500_8700.SplitData.node2375 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2376
  · rfl
  · rfl
  · rfl

def B2374 : Block := .branch 168 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 680564734317245902012335240424800149512, 1329227995784915872903807060280442896, 5708990770823839524233143877797980545531379744, 11199373260101926709506585079794905130729536] ![(.leaf 0 (Common.fact 909).pointIds 909), (.leaf 1 (Common.fact 914).pointIds 914), (.leaf 2 (Common.fact 915).pointIds 915), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 574).pointIds 574), B2375]
theorem treeEq2374 : B2374.tree = HexagonCover.NBand.M8500_8700.SplitData.node2374 := by
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
  · exact treeEq2375

def B2373 : Block := .branch 152 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 680564734317245902012335240424800149512, 1393797904136159731261855295847582874566672, 393248, 11199415795397791826814518001620834101755968] ![(.leaf 0 (Common.fact 354).pointIds 354), (.leaf 1 (Common.fact 355).pointIds 355), (.leaf 2 (Common.fact 356).pointIds 356), (.leaf 3 (Common.fact 357).pointIds 357), (.leaf 4 (Common.fact 358).pointIds 358), B2374, (.leaf 6 (Common.fact 602).pointIds 602)]
theorem treeEq2373 : B2373.tree = HexagonCover.NBand.M8500_8700.SplitData.node2373 := by
  change Tree.branch (152 : Fin 175) _ = Tree.branch (152 : Fin 175) _
  apply congrArg (Tree.branch (152 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2374
  · rfl

def B2351 : Block := .branch 132 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 680564734317245902012335240424800149512, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B2352, (.leaf 5 (Common.fact 329).pointIds 329), B2373]
theorem treeEq2351 : B2351.tree = HexagonCover.NBand.M8500_8700.SplitData.node2351 := by
  change Tree.branch (132 : Fin 175) _ = Tree.branch (132 : Fin 175) _
  apply congrArg (Tree.branch (132 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2352
  · rfl
  · exact treeEq2373

def B2383 : Block := .branch 169 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 922).pointIds 922), (.leaf 2 (Common.fact 923).pointIds 923), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq2383 : B2383.tree = HexagonCover.NBand.M8500_8700.SplitData.node2383 := by
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

def B2382 : Block := .branch 170 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 920).pointIds 920), (.leaf 2 (Common.fact 921).pointIds 921), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B2383, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq2382 : B2382.tree = HexagonCover.NBand.M8500_8700.SplitData.node2382 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2383
  · rfl

def B2381 : Block := .branch 163 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 684553066866338991398914202356418707472, 233840261972944466912589573234605283144949207269408, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 618).pointIds 618), (.leaf 5 (Common.fact 387).pointIds 387), B2382]
theorem treeEq2381 : B2381.tree = HexagonCover.NBand.M8500_8700.SplitData.node2381 := by
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
  · exact treeEq2382

def B2380 : Block := .branch 165 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 684553066866338991398914202356418707472, 187072209578355573530071658587684226515959365894176, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 617).pointIds 617), B2381, (.leaf 0 [] 0)]
theorem treeEq2380 : B2380.tree = HexagonCover.NBand.M8500_8700.SplitData.node2380 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2381
  · rfl

def B2379 : Block := .branch 167 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 684553066866338991398914202356418707472, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 616).pointIds 616), B2380, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq2379 : B2379.tree = HexagonCover.NBand.M8500_8700.SplitData.node2379 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2380
  · rfl

def B2350 : Block := .branch 129 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 475368975085586025561263726600, 1393800563241188408410454557028015476408336, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), (.leaf 2 (Common.fact 322).pointIds 322), B2351, B2379, (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 6 (Common.fact 324).pointIds 324)]
theorem treeEq2350 : B2350.tree = HexagonCover.NBand.M8500_8700.SplitData.node2350 := by
  change Tree.branch (129 : Fin 175) _ = Tree.branch (129 : Fin 175) _
  apply congrArg (Tree.branch (129 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2351
  · exact treeEq2379
  · rfl
  · rfl

theorem accepted2350 : B2350.accepted = true := by decide +kernel
theorem checked2350 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node2350 (maskNeeds ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 475368975085586025561263726600, 1393800563241188408410454557028015476408336, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq2350]
  exact B2350.sound accepted2350
#print axioms checked2350

def B2412 : Block := .branch 169 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 3367299783604329065772481548669487163363265418362944] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 922).pointIds 922), (.leaf 2 (Common.fact 923).pointIds 923), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 444).pointIds 444)]
theorem treeEq2412 : B2412.tree = HexagonCover.NBand.M8500_8700.SplitData.node2412 := by
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

def B2411 : Block := .branch 170 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 3367299783604329065772481548669487163363265418362944] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 920).pointIds 920), (.leaf 2 (Common.fact 921).pointIds 921), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B2412, (.leaf 6 (Common.fact 440).pointIds 440)]
theorem treeEq2411 : B2411.tree = HexagonCover.NBand.M8500_8700.SplitData.node2411 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2412
  · rfl

def B2410 : Block := .branch 171 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 5986310706855827496689809430367476432546391608287240, 1329227995784915872903807060280442896, 393248, 374144430350639889291335011266539539107915570348096] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 578).pointIds 578), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B2411]
theorem treeEq2410 : B2410.tree = HexagonCover.NBand.M8500_8700.SplitData.node2410 := by
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
  · exact treeEq2411

def B2409 : Block := .branch 172 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 393248, 374144430350639889291335011266539539107915570348096] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 916).pointIds 916), (.leaf 2 (Common.fact 917).pointIds 917), B2410, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 452).pointIds 452)]
theorem treeEq2409 : B2409.tree = HexagonCover.NBand.M8500_8700.SplitData.node2409 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2410
  · rfl
  · rfl
  · rfl

def B2408 : Block := .branch 168 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 22300745198530623141535718272648361506373664, 11193928742231191694091171086075996839346240] ![(.leaf 0 (Common.fact 909).pointIds 909), (.leaf 1 (Common.fact 914).pointIds 914), (.leaf 2 (Common.fact 915).pointIds 915), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 517).pointIds 517), B2409]
theorem treeEq2408 : B2408.tree = HexagonCover.NBand.M8500_8700.SplitData.node2408 := by
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
  · exact treeEq2409

def B2414 : Block := .branch 171 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 5986310706855827496689650974042447903871204520386568, 1329227995784915872903807060280442896, 393248, 33451160338284096688146337959329517314506816] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 578).pointIds 578), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 684).pointIds 684)]
theorem treeEq2414 : B2414.tree = HexagonCover.NBand.M8500_8700.SplitData.node2414 := by
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

def B2413 : Block := .branch 172 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 348449143727357899236552655360504824356872, 1329227995784915872903807060280442896, 393248, 33451160338284096688146337959329517314506816] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 916).pointIds 916), (.leaf 2 (Common.fact 917).pointIds 917), B2414, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 683).pointIds 683)]
theorem treeEq2413 : B2413.tree = HexagonCover.NBand.M8500_8700.SplitData.node2413 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2414
  · rfl
  · rfl
  · rfl

def B2407 : Block := .branch 144 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 340).pointIds 340), (.leaf 1 (Common.fact 341).pointIds 341), (.leaf 2 (Common.fact 342).pointIds 342), (.leaf 3 (Common.fact 343).pointIds 343), (.leaf 4 (Common.fact 344).pointIds 344), B2408, B2413]
theorem treeEq2407 : B2407.tree = HexagonCover.NBand.M8500_8700.SplitData.node2407 := by
  change Tree.branch (144 : Fin 175) _ = Tree.branch (144 : Fin 175) _
  apply congrArg (Tree.branch (144 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2408
  · exact treeEq2413

def B2420 : Block := .branch 169 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 3367299789179515365405137334053416731525355794858048] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 922).pointIds 922), (.leaf 2 (Common.fact 923).pointIds 923), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 586).pointIds 586)]
theorem treeEq2420 : B2420.tree = HexagonCover.NBand.M8500_8700.SplitData.node2420 := by
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

def B2419 : Block := .branch 170 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 3367299789179515365405137334053416731525355794858048] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 920).pointIds 920), (.leaf 2 (Common.fact 921).pointIds 921), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B2420, (.leaf 6 (Common.fact 583).pointIds 583)]
theorem treeEq2419 : B2419.tree = HexagonCover.NBand.M8500_8700.SplitData.node2419 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2420
  · rfl

def B2418 : Block := .branch 171 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 5986310706855827496689809430367476432546391608287240, 1329227995784915872903807060280442896, 393248, 374144435925826188923990796650469107270005946843200] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 578).pointIds 578), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B2419]
theorem treeEq2418 : B2418.tree = HexagonCover.NBand.M8500_8700.SplitData.node2418 := by
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
  · exact treeEq2419

def B2417 : Block := .branch 172 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 393248, 374144435925826188923990796650469107270005946843200] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 916).pointIds 916), (.leaf 2 (Common.fact 917).pointIds 917), B2418, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 577).pointIds 577)]
theorem treeEq2417 : B2417.tree = HexagonCover.NBand.M8500_8700.SplitData.node2417 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2418
  · rfl
  · rfl
  · rfl

def B2416 : Block := .branch 168 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 5708990770823839524233143877797980545531379744, 16769115041863847479475100654238087215841344] ![(.leaf 0 (Common.fact 909).pointIds 909), (.leaf 1 (Common.fact 914).pointIds 914), (.leaf 2 (Common.fact 915).pointIds 915), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 574).pointIds 574), B2417]
theorem treeEq2416 : B2416.tree = HexagonCover.NBand.M8500_8700.SplitData.node2416 := by
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
  · exact treeEq2417

def B2415 : Block := .branch 152 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 16769157582352009455317861204594512516087872] ![(.leaf 0 (Common.fact 354).pointIds 354), (.leaf 1 (Common.fact 355).pointIds 355), (.leaf 2 (Common.fact 356).pointIds 356), (.leaf 3 (Common.fact 357).pointIds 357), (.leaf 4 (Common.fact 358).pointIds 358), B2416, (.leaf 6 (Common.fact 685).pointIds 685)]
theorem treeEq2415 : B2415.tree = HexagonCover.NBand.M8500_8700.SplitData.node2415 := by
  change Tree.branch (152 : Fin 175) _ = Tree.branch (152 : Fin 175) _
  apply congrArg (Tree.branch (152 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2416
  · rfl

def B2406 : Block := .branch 142 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), B2407, (.leaf 5 (Common.fact 339).pointIds 339), B2415]
theorem treeEq2406 : B2406.tree = HexagonCover.NBand.M8500_8700.SplitData.node2406 := by
  change Tree.branch (142 : Fin 175) _ = Tree.branch (142 : Fin 175) _
  apply congrArg (Tree.branch (142 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2407
  · rfl
  · exact treeEq2415

theorem accepted2406 : B2406.accepted = true := by decide +kernel
theorem checked2406 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node2406 (maskNeeds ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 11193971282719353669933931636432422139592768]) := by
  rw [← treeEq2406]
  exact B2406.sound accepted2406
#print axioms checked2406

def Tip2403_2406 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node2406 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 11193971282719353669933931636432422139592768] checked2406
def B2425 : Block := .branch 169 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618506064983148595661900589669599936576] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 922).pointIds 922), (.leaf 2 (Common.fact 923).pointIds 923), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 688).pointIds 688)]
theorem treeEq2425 : B2425.tree = HexagonCover.NBand.M8500_8700.SplitData.node2425 := by
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

def B2424 : Block := .branch 170 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618506064983148595661900589669599936576] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 920).pointIds 920), (.leaf 2 (Common.fact 921).pointIds 921), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B2425, (.leaf 6 (Common.fact 686).pointIds 686)]
theorem treeEq2424 : B2424.tree = HexagonCover.NBand.M8500_8700.SplitData.node2424 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2425
  · rfl

def B2423 : Block := .branch 163 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 353894991474808894234635949102411261509648, 233840261972944466912589573234605283144949207269408, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 589).pointIds 589), (.leaf 5 (Common.fact 387).pointIds 387), B2424]
theorem treeEq2423 : B2423.tree = HexagonCover.NBand.M8500_8700.SplitData.node2423 := by
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
  · exact treeEq2424

def B2422 : Block := .branch 165 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 353894991474808894234635949102411261509648, 187072209578355573530071658587684226515959365894176, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 588).pointIds 588), B2423, (.leaf 0 [] 0)]
theorem treeEq2422 : B2422.tree = HexagonCover.NBand.M8500_8700.SplitData.node2422 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2423
  · rfl

def B2421 : Block := .branch 167 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 353894991474808894234635949102411261509648, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 587).pointIds 587), B2422, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq2421 : B2421.tree = HexagonCover.NBand.M8500_8700.SplitData.node2421 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2422
  · rfl

def B2405 : Block := .branch 138 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 475368975085586025561263726600, 1399242422655931853994122743132803207102480, 393248, 11226638389943763762426415598745871887892544] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), Tip2403_2406, B2421, (.leaf 5 (Common.fact 333).pointIds 333), (.leaf 6 (Common.fact 334).pointIds 334)]
theorem treeEq2405 : B2405.tree = HexagonCover.NBand.M8500_8700.SplitData.node2405 := by
  change Tree.branch (138 : Fin 175) _ = Tree.branch (138 : Fin 175) _
  apply congrArg (Tree.branch (138 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2421
  · rfl
  · rfl

def B2431 : Block := .branch 169 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 3367299783609773583643216564084901157082173709746240] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 922).pointIds 922), (.leaf 2 (Common.fact 923).pointIds 923), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 615).pointIds 615)]
theorem treeEq2431 : B2431.tree = HexagonCover.NBand.M8500_8700.SplitData.node2431 := by
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

def B2430 : Block := .branch 170 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 3367299783609773583643216564084901157082173709746240] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 920).pointIds 920), (.leaf 2 (Common.fact 921).pointIds 921), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B2431, (.leaf 6 (Common.fact 612).pointIds 612)]
theorem treeEq2430 : B2430.tree = HexagonCover.NBand.M8500_8700.SplitData.node2430 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2431
  · rfl

def B2429 : Block := .branch 171 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 5986310706508058917696610320707907583751124496179208, 1329227995784915872903807060280442896, 393248, 374144430356084407162070026681953532826823861731392] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 608).pointIds 608), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B2430]
theorem treeEq2429 : B2429.tree = HexagonCover.NBand.M8500_8700.SplitData.node2429 := by
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
  · exact treeEq2430

def B2428 : Block := .branch 172 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 680564734317245902012335240424800149512, 1329227995784915872903807060280442896, 393248, 374144430356084407162070026681953532826823861731392] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 916).pointIds 916), (.leaf 2 (Common.fact 917).pointIds 917), B2429, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 607).pointIds 607)]
theorem treeEq2428 : B2428.tree = HexagonCover.NBand.M8500_8700.SplitData.node2428 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2429
  · rfl
  · rfl
  · rfl

def B2427 : Block := .branch 168 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 680564734317245902012335240424800149512, 1329227995784915872903807060280442896, 5708990770823839524233143877797980545531379744, 11199373260101926709506585079794905130729536] ![(.leaf 0 (Common.fact 909).pointIds 909), (.leaf 1 (Common.fact 914).pointIds 914), (.leaf 2 (Common.fact 915).pointIds 915), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 574).pointIds 574), B2428]
theorem treeEq2427 : B2427.tree = HexagonCover.NBand.M8500_8700.SplitData.node2427 := by
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
  · exact treeEq2428

def B2426 : Block := .branch 152 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 680564734317245902012335240424800149512, 1393797904136159731261855295847582874566672, 393248, 11199415800590088685349345630151330430976064] ![(.leaf 0 (Common.fact 354).pointIds 354), (.leaf 1 (Common.fact 355).pointIds 355), (.leaf 2 (Common.fact 356).pointIds 356), (.leaf 3 (Common.fact 357).pointIds 357), (.leaf 4 (Common.fact 358).pointIds 358), B2427, (.leaf 6 (Common.fact 689).pointIds 689)]
theorem treeEq2426 : B2426.tree = HexagonCover.NBand.M8500_8700.SplitData.node2426 := by
  change Tree.branch (152 : Fin 175) _ = Tree.branch (152 : Fin 175) _
  apply congrArg (Tree.branch (152 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2427
  · rfl

def B2404 : Block := .branch 132 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 680564734317245902012335240424800149512, 1393797904785196838578708749413894915719184, 393248, 11226638389943763762426415598745871887892544] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B2405, (.leaf 5 (Common.fact 329).pointIds 329), B2426]
theorem treeEq2404 : B2404.tree = HexagonCover.NBand.M8500_8700.SplitData.node2404 := by
  change Tree.branch (132 : Fin 175) _ = Tree.branch (132 : Fin 175) _
  apply congrArg (Tree.branch (132 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2405
  · rfl
  · exact treeEq2426

def B2436 : Block := .branch 169 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618506064983148595661900589669599936576] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 922).pointIds 922), (.leaf 2 (Common.fact 923).pointIds 923), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 688).pointIds 688)]
theorem treeEq2436 : B2436.tree = HexagonCover.NBand.M8500_8700.SplitData.node2436 := by
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

def B2435 : Block := .branch 170 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618506064983148595661900589669599936576] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 920).pointIds 920), (.leaf 2 (Common.fact 921).pointIds 921), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B2436, (.leaf 6 (Common.fact 686).pointIds 686)]
theorem treeEq2435 : B2435.tree = HexagonCover.NBand.M8500_8700.SplitData.node2435 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2436
  · rfl

def B2434 : Block := .branch 163 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 684553066866338991398914202356418707472, 233840261972944466912589573234605283144949207269408, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 618).pointIds 618), (.leaf 5 (Common.fact 387).pointIds 387), B2435]
theorem treeEq2434 : B2434.tree = HexagonCover.NBand.M8500_8700.SplitData.node2434 := by
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
  · exact treeEq2435

def B2433 : Block := .branch 165 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 684553066866338991398914202356418707472, 187072209578355573530071658587684226515959365894176, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 617).pointIds 617), B2434, (.leaf 0 [] 0)]
theorem treeEq2433 : B2433.tree = HexagonCover.NBand.M8500_8700.SplitData.node2433 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2434
  · rfl

def B2432 : Block := .branch 167 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 684553066866338991398914202356418707472, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 616).pointIds 616), B2433, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq2432 : B2432.tree = HexagonCover.NBand.M8500_8700.SplitData.node2432 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2433
  · rfl

def B2403 : Block := .branch 129 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 475368975085586025561263726600, 1393800563241188408410454557028015476408336, 393248, 11226638389943763762426415598745871887892544] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), (.leaf 2 (Common.fact 322).pointIds 322), B2404, B2432, (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 6 (Common.fact 324).pointIds 324)]
theorem treeEq2403 : B2403.tree = HexagonCover.NBand.M8500_8700.SplitData.node2403 := by
  change Tree.branch (129 : Fin 175) _ = Tree.branch (129 : Fin 175) _
  apply congrArg (Tree.branch (129 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2404
  · exact treeEq2432
  · rfl
  · rfl

theorem accepted2403 : B2403.accepted = true := by decide +kernel
theorem checked2403 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node2403 (maskNeeds ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 475368975085586025561263726600, 1393800563241188408410454557028015476408336, 393248, 11226638389943763762426415598745871887892544]) := by
  rw [← treeEq2403]
  exact B2403.sound accepted2403
#print axioms checked2403

end HexagonCover.NBand.M8500_8700.SplitTree.Run0032
