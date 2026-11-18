import HexagonCover.NBand.M8500_8700.SplitData
import HexagonCover.NBand.M8500_8700.SplitTree.Run0026
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8500_8700.SplitTree.Run0027
open OwnerTree HexagonCover.NBand.M8500_8700

abbrev Block := Chunk (n := 175) (Certificate := Fin 1173) (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck

def B1998 : Block := .branch 169 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 3367299783604329065772481548669487163363265418362944] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 922).pointIds 922), (.leaf 2 (Common.fact 923).pointIds 923), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 444).pointIds 444)]
theorem treeEq1998 : B1998.tree = HexagonCover.NBand.M8500_8700.SplitData.node1998 := by
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

def B1997 : Block := .branch 170 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 3367299783604329065772481548669487163363265418362944] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 920).pointIds 920), (.leaf 2 (Common.fact 921).pointIds 921), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1998, (.leaf 6 (Common.fact 440).pointIds 440)]
theorem treeEq1997 : B1997.tree = HexagonCover.NBand.M8500_8700.SplitData.node1997 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1998
  · rfl

def B1996 : Block := .branch 171 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 5986310706855827496689809430367476432546391608287240, 1329227995784915872903807060280442896, 393248, 374144430350639889291335011266539539107915570348096] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 578).pointIds 578), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B1997]
theorem treeEq1996 : B1996.tree = HexagonCover.NBand.M8500_8700.SplitData.node1996 := by
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
  · exact treeEq1997

def B1995 : Block := .branch 172 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 393248, 374144430350639889291335011266539539107915570348096] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 916).pointIds 916), (.leaf 2 (Common.fact 917).pointIds 917), B1996, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 452).pointIds 452)]
theorem treeEq1995 : B1995.tree = HexagonCover.NBand.M8500_8700.SplitData.node1995 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1996
  · rfl
  · rfl
  · rfl

def B1994 : Block := .branch 168 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 22300745198530623141535718272648361506373664, 11193928742231191694091171086075996839346240] ![(.leaf 0 (Common.fact 909).pointIds 909), (.leaf 1 (Common.fact 914).pointIds 914), (.leaf 2 (Common.fact 915).pointIds 915), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 517).pointIds 517), B1995]
theorem treeEq1994 : B1994.tree = HexagonCover.NBand.M8500_8700.SplitData.node1994 := by
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
  · exact treeEq1995

def B2000 : Block := .branch 171 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 5986310706855827496689650974042447903871204520386568, 1329227995784915872903807060280442896, 393248, 33451160338284096688146337959329517314506816] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 578).pointIds 578), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 684).pointIds 684)]
theorem treeEq2000 : B2000.tree = HexagonCover.NBand.M8500_8700.SplitData.node2000 := by
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

def B1999 : Block := .branch 172 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 348449143727357899236552655360504824356872, 1329227995784915872903807060280442896, 393248, 33451160338284096688146337959329517314506816] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 916).pointIds 916), (.leaf 2 (Common.fact 917).pointIds 917), B2000, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 683).pointIds 683)]
theorem treeEq1999 : B1999.tree = HexagonCover.NBand.M8500_8700.SplitData.node1999 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2000
  · rfl
  · rfl
  · rfl

def B1993 : Block := .branch 144 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 340).pointIds 340), (.leaf 1 (Common.fact 341).pointIds 341), (.leaf 2 (Common.fact 342).pointIds 342), (.leaf 3 (Common.fact 343).pointIds 343), (.leaf 4 (Common.fact 344).pointIds 344), B1994, B1999]
theorem treeEq1993 : B1993.tree = HexagonCover.NBand.M8500_8700.SplitData.node1993 := by
  change Tree.branch (144 : Fin 175) _ = Tree.branch (144 : Fin 175) _
  apply congrArg (Tree.branch (144 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1994
  · exact treeEq1999

def B2006 : Block := .branch 169 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 3367299789179515365405137334053416731525355794858048] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 922).pointIds 922), (.leaf 2 (Common.fact 923).pointIds 923), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 586).pointIds 586)]
theorem treeEq2006 : B2006.tree = HexagonCover.NBand.M8500_8700.SplitData.node2006 := by
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

def B2005 : Block := .branch 170 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 3367299789179515365405137334053416731525355794858048] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 920).pointIds 920), (.leaf 2 (Common.fact 921).pointIds 921), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B2006, (.leaf 6 (Common.fact 583).pointIds 583)]
theorem treeEq2005 : B2005.tree = HexagonCover.NBand.M8500_8700.SplitData.node2005 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2006
  · rfl

def B2004 : Block := .branch 171 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 5986310706855827496689809430367476432546391608287240, 1329227995784915872903807060280442896, 393248, 374144435925826188923990796650469107270005946843200] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 578).pointIds 578), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B2005]
theorem treeEq2004 : B2004.tree = HexagonCover.NBand.M8500_8700.SplitData.node2004 := by
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
  · exact treeEq2005

def B2003 : Block := .branch 172 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 393248, 374144435925826188923990796650469107270005946843200] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 916).pointIds 916), (.leaf 2 (Common.fact 917).pointIds 917), B2004, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 577).pointIds 577)]
theorem treeEq2003 : B2003.tree = HexagonCover.NBand.M8500_8700.SplitData.node2003 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2004
  · rfl
  · rfl
  · rfl

def B2002 : Block := .branch 168 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 5708990770823839524233143877797980545531379744, 16769115041863847479475100654238087215841344] ![(.leaf 0 (Common.fact 909).pointIds 909), (.leaf 1 (Common.fact 914).pointIds 914), (.leaf 2 (Common.fact 915).pointIds 915), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 574).pointIds 574), B2003]
theorem treeEq2002 : B2002.tree = HexagonCover.NBand.M8500_8700.SplitData.node2002 := by
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
  · exact treeEq2003

def B2001 : Block := .branch 152 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 16769157582352009455317861204594512516087872] ![(.leaf 0 (Common.fact 354).pointIds 354), (.leaf 1 (Common.fact 355).pointIds 355), (.leaf 2 (Common.fact 356).pointIds 356), (.leaf 3 (Common.fact 357).pointIds 357), (.leaf 4 (Common.fact 358).pointIds 358), B2002, (.leaf 6 (Common.fact 685).pointIds 685)]
theorem treeEq2001 : B2001.tree = HexagonCover.NBand.M8500_8700.SplitData.node2001 := by
  change Tree.branch (152 : Fin 175) _ = Tree.branch (152 : Fin 175) _
  apply congrArg (Tree.branch (152 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2002
  · rfl

def B1992 : Block := .branch 142 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), B1993, (.leaf 5 (Common.fact 339).pointIds 339), B2001]
theorem treeEq1992 : B1992.tree = HexagonCover.NBand.M8500_8700.SplitData.node1992 := by
  change Tree.branch (142 : Fin 175) _ = Tree.branch (142 : Fin 175) _
  apply congrArg (Tree.branch (142 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1993
  · rfl
  · exact treeEq2001

theorem accepted1992 : B1992.accepted = true := by decide +kernel
theorem checked1992 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node1992 (maskNeeds ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 11193971282719353669933931636432422139592768]) := by
  rw [← treeEq1992]
  exact B1992.sound accepted1992
#print axioms checked1992

def Tip1989_1992 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node1992 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 11193971282719353669933931636432422139592768] checked1992
def B2011 : Block := .branch 169 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618506064983148595661900589669599936576] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 922).pointIds 922), (.leaf 2 (Common.fact 923).pointIds 923), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 688).pointIds 688)]
theorem treeEq2011 : B2011.tree = HexagonCover.NBand.M8500_8700.SplitData.node2011 := by
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

def B2010 : Block := .branch 170 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618506064983148595661900589669599936576] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 920).pointIds 920), (.leaf 2 (Common.fact 921).pointIds 921), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B2011, (.leaf 6 (Common.fact 686).pointIds 686)]
theorem treeEq2010 : B2010.tree = HexagonCover.NBand.M8500_8700.SplitData.node2010 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2011
  · rfl

def B2009 : Block := .branch 163 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 353894991474808894234635949102411261509648, 233840261972944466912589573234605283144949207269408, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 589).pointIds 589), (.leaf 5 (Common.fact 387).pointIds 387), B2010]
theorem treeEq2009 : B2009.tree = HexagonCover.NBand.M8500_8700.SplitData.node2009 := by
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
  · exact treeEq2010

def B2008 : Block := .branch 165 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 353894991474808894234635949102411261509648, 187072209578355573530071658587684226515959365894176, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 588).pointIds 588), B2009, (.leaf 0 [] 0)]
theorem treeEq2008 : B2008.tree = HexagonCover.NBand.M8500_8700.SplitData.node2008 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2009
  · rfl

def B2007 : Block := .branch 167 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 353894991474808894234635949102411261509648, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 587).pointIds 587), B2008, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq2007 : B2007.tree = HexagonCover.NBand.M8500_8700.SplitData.node2007 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2008
  · rfl

def B1991 : Block := .branch 138 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 475368975085586025561263726600, 1399242422655931853994122743132803207102480, 393248, 11226638389943763762426415598745871887892544] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), Tip1989_1992, B2007, (.leaf 5 (Common.fact 333).pointIds 333), (.leaf 6 (Common.fact 334).pointIds 334)]
theorem treeEq1991 : B1991.tree = HexagonCover.NBand.M8500_8700.SplitData.node1991 := by
  change Tree.branch (138 : Fin 175) _ = Tree.branch (138 : Fin 175) _
  apply congrArg (Tree.branch (138 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2007
  · rfl
  · rfl

def B2017 : Block := .branch 169 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 3367299783609773583643216564084901157082173709746240] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 922).pointIds 922), (.leaf 2 (Common.fact 923).pointIds 923), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 615).pointIds 615)]
theorem treeEq2017 : B2017.tree = HexagonCover.NBand.M8500_8700.SplitData.node2017 := by
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

def B2016 : Block := .branch 170 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 3367299783609773583643216564084901157082173709746240] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 920).pointIds 920), (.leaf 2 (Common.fact 921).pointIds 921), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B2017, (.leaf 6 (Common.fact 612).pointIds 612)]
theorem treeEq2016 : B2016.tree = HexagonCover.NBand.M8500_8700.SplitData.node2016 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2017
  · rfl

def B2015 : Block := .branch 171 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 5986310706508058917696610320707907583751124496179208, 1329227995784915872903807060280442896, 393248, 374144430356084407162070026681953532826823861731392] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 608).pointIds 608), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B2016]
theorem treeEq2015 : B2015.tree = HexagonCover.NBand.M8500_8700.SplitData.node2015 := by
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
  · exact treeEq2016

def B2014 : Block := .branch 172 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 680564734317245902012335240424800149512, 1329227995784915872903807060280442896, 393248, 374144430356084407162070026681953532826823861731392] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 916).pointIds 916), (.leaf 2 (Common.fact 917).pointIds 917), B2015, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 607).pointIds 607)]
theorem treeEq2014 : B2014.tree = HexagonCover.NBand.M8500_8700.SplitData.node2014 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2015
  · rfl
  · rfl
  · rfl

def B2013 : Block := .branch 168 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 680564734317245902012335240424800149512, 1329227995784915872903807060280442896, 5708990770823839524233143877797980545531379744, 11199373260101926709506585079794905130729536] ![(.leaf 0 (Common.fact 909).pointIds 909), (.leaf 1 (Common.fact 914).pointIds 914), (.leaf 2 (Common.fact 915).pointIds 915), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 574).pointIds 574), B2014]
theorem treeEq2013 : B2013.tree = HexagonCover.NBand.M8500_8700.SplitData.node2013 := by
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
  · exact treeEq2014

def B2012 : Block := .branch 152 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 680564734317245902012335240424800149512, 1393797904136159731261855295847582874566672, 393248, 11199415800590088685349345630151330430976064] ![(.leaf 0 (Common.fact 354).pointIds 354), (.leaf 1 (Common.fact 355).pointIds 355), (.leaf 2 (Common.fact 356).pointIds 356), (.leaf 3 (Common.fact 357).pointIds 357), (.leaf 4 (Common.fact 358).pointIds 358), B2013, (.leaf 6 (Common.fact 689).pointIds 689)]
theorem treeEq2012 : B2012.tree = HexagonCover.NBand.M8500_8700.SplitData.node2012 := by
  change Tree.branch (152 : Fin 175) _ = Tree.branch (152 : Fin 175) _
  apply congrArg (Tree.branch (152 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2013
  · rfl

def B1990 : Block := .branch 132 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 680564734317245902012335240424800149512, 1393797904785196838578708749413894915719184, 393248, 11226638389943763762426415598745871887892544] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B1991, (.leaf 5 (Common.fact 329).pointIds 329), B2012]
theorem treeEq1990 : B1990.tree = HexagonCover.NBand.M8500_8700.SplitData.node1990 := by
  change Tree.branch (132 : Fin 175) _ = Tree.branch (132 : Fin 175) _
  apply congrArg (Tree.branch (132 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1991
  · rfl
  · exact treeEq2012

def B2022 : Block := .branch 169 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618506064983148595661900589669599936576] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 922).pointIds 922), (.leaf 2 (Common.fact 923).pointIds 923), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 688).pointIds 688)]
theorem treeEq2022 : B2022.tree = HexagonCover.NBand.M8500_8700.SplitData.node2022 := by
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

def B2021 : Block := .branch 170 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618506064983148595661900589669599936576] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 920).pointIds 920), (.leaf 2 (Common.fact 921).pointIds 921), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B2022, (.leaf 6 (Common.fact 686).pointIds 686)]
theorem treeEq2021 : B2021.tree = HexagonCover.NBand.M8500_8700.SplitData.node2021 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2022
  · rfl

def B2020 : Block := .branch 163 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 684553066866338991398914202356418707472, 233840261972944466912589573234605283144949207269408, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 618).pointIds 618), (.leaf 5 (Common.fact 387).pointIds 387), B2021]
theorem treeEq2020 : B2020.tree = HexagonCover.NBand.M8500_8700.SplitData.node2020 := by
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
  · exact treeEq2021

def B2019 : Block := .branch 165 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 684553066866338991398914202356418707472, 187072209578355573530071658587684226515959365894176, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 617).pointIds 617), B2020, (.leaf 0 [] 0)]
theorem treeEq2019 : B2019.tree = HexagonCover.NBand.M8500_8700.SplitData.node2019 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2020
  · rfl

def B2018 : Block := .branch 167 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 684553066866338991398914202356418707472, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 616).pointIds 616), B2019, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq2018 : B2018.tree = HexagonCover.NBand.M8500_8700.SplitData.node2018 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2019
  · rfl

def B1989 : Block := .branch 129 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 475368975085586025561263726600, 1393800563241188408410454557028015476408336, 393248, 11226638389943763762426415598745871887892544] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), (.leaf 2 (Common.fact 322).pointIds 322), B1990, B2018, (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 6 (Common.fact 324).pointIds 324)]
theorem treeEq1989 : B1989.tree = HexagonCover.NBand.M8500_8700.SplitData.node1989 := by
  change Tree.branch (129 : Fin 175) _ = Tree.branch (129 : Fin 175) _
  apply congrArg (Tree.branch (129 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1990
  · exact treeEq2018
  · rfl
  · rfl

theorem accepted1989 : B1989.accepted = true := by decide +kernel
theorem checked1989 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node1989 (maskNeeds ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 475368975085586025561263726600, 1393800563241188408410454557028015476408336, 393248, 11226638389943763762426415598745871887892544]) := by
  rw [← treeEq1989]
  exact B1989.sound accepted1989
#print axioms checked1989

def Tip1932_1936 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node1936 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 475368975085586025561263726600, 1393800563241188408410454557028015476408336, 393248, 11226638384751466903891587970215375558672448] HexagonCover.NBand.M8500_8700.SplitTree.Run0026.checked1936
def B1973 : Block := .branch 171 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 5986310706507379017576607879913888757764604012027912, 1329227995784915872903807060280442896, 393248, 748288849507353694807469898273653799753954862039104] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 636).pointIds 636), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 692).pointIds 692)]
theorem treeEq1973 : B1973.tree = HexagonCover.NBand.M8500_8700.SplitData.node1973 := by
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

def B1972 : Block := .branch 172 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 664614314805107993509253904315998216, 1329227995784915872903807060280442896, 393248, 748288849507353694807469898273653799753954862039104] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 916).pointIds 916), (.leaf 2 (Common.fact 917).pointIds 917), B1973, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 691).pointIds 691)]
theorem treeEq1972 : B1972.tree = HexagonCover.NBand.M8500_8700.SplitData.node1972 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1973
  · rfl
  · rfl
  · rfl

def B1971 : Block := .branch 169 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 664614473261433022037929091403898888, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 11193931400687183263922916893690117400035392] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 922).pointIds 922), (.leaf 2 (Common.fact 923).pointIds 923), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), B1972]
theorem treeEq1971 : B1971.tree = HexagonCover.NBand.M8500_8700.SplitData.node1971 := by
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
  · exact treeEq1972

def B1970 : Block := .branch 170 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 664614473261433022037929091403898888, 1329227995784915872903807060280442896, 393248, 11193973935983048381230849815516046371061824] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 920).pointIds 920), (.leaf 2 (Common.fact 921).pointIds 921), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1971, (.leaf 6 (Common.fact 643).pointIds 643)]
theorem treeEq1970 : B1970.tree = HexagonCover.NBand.M8500_8700.SplitData.node1970 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1971
  · rfl

def B1935 : Block := .branch 121 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 664614473261433022037929091403898888, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 315).pointIds 315), (.leaf 1 (Common.fact 316).pointIds 316), (.leaf 2 (Common.fact 317).pointIds 317), (.leaf 3 (Common.fact 318).pointIds 318), Tip1932_1936, (.leaf 5 (Common.fact 319).pointIds 319), B1970]
theorem treeEq1935 : B1935.tree = HexagonCover.NBand.M8500_8700.SplitData.node1935 := by
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
  · exact treeEq1970

def B1978 : Block := .branch 169 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 922).pointIds 922), (.leaf 2 (Common.fact 923).pointIds 923), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq1978 : B1978.tree = HexagonCover.NBand.M8500_8700.SplitData.node1978 := by
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

def B1977 : Block := .branch 170 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 920).pointIds 920), (.leaf 2 (Common.fact 921).pointIds 921), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1978, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq1977 : B1977.tree = HexagonCover.NBand.M8500_8700.SplitData.node1977 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1978
  · rfl

def B1976 : Block := .branch 163 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1994491030784690662809276902461767696, 233840261972944466912589573234605283144949207269408, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 387).pointIds 387), B1977]
theorem treeEq1976 : B1976.tree = HexagonCover.NBand.M8500_8700.SplitData.node1976 := by
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
  · exact treeEq1977

def B1975 : Block := .branch 165 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1994491030784690662809276902461767696, 187072209578355573530071658587684226515959365894176, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 645).pointIds 645), B1976, (.leaf 0 [] 0)]
theorem treeEq1975 : B1975.tree = HexagonCover.NBand.M8500_8700.SplitData.node1975 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1976
  · rfl

def B1974 : Block := .branch 167 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1994491030784690662809276902461767696, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 644).pointIds 644), B1975, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq1974 : B1974.tree = HexagonCover.NBand.M8500_8700.SplitData.node1974 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1975
  · rfl

def B1934 : Block := .branch 119 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 475368975085586025561263726600, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 310).pointIds 310), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), B1935, B1974, (.leaf 5 (Common.fact 313).pointIds 313), (.leaf 6 (Common.fact 314).pointIds 314)]
theorem treeEq1934 : B1934.tree = HexagonCover.NBand.M8500_8700.SplitData.node1934 := by
  change Tree.branch (119 : Fin 175) _ = Tree.branch (119 : Fin 175) _
  apply congrArg (Tree.branch (119 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1935
  · exact treeEq1974
  · rfl
  · rfl

def B1980 : Block := .branch 171 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 5986310706507378353287128541114379032644229892431880, 1329227995784915872903807060280442896, 393248, 11193971298296244245538414522023911127253056] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq1980 : B1980.tree = HexagonCover.NBand.M8500_8700.SplitData.node1980 := by
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

def B1979 : Block := .branch 172 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 324835466308483784133530196402184, 1329227995784915872903807060280442896, 393248, 11193971298296244245538414522023911127253056] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 916).pointIds 916), (.leaf 2 (Common.fact 917).pointIds 917), B1980, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 666).pointIds 666)]
theorem treeEq1979 : B1979.tree = HexagonCover.NBand.M8500_8700.SplitData.node1979 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1980
  · rfl
  · rfl
  · rfl

def B1933 : Block := .branch 114 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 324993922633512312808717284302856, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448] ![B1934, (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 308).pointIds 308), (.leaf 5 (Common.fact 309).pointIds 309), B1979]
theorem treeEq1933 : B1933.tree = HexagonCover.NBand.M8500_8700.SplitData.node1933 := by
  change Tree.branch (114 : Fin 175) _ = Tree.branch (114 : Fin 175) _
  apply congrArg (Tree.branch (114 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq1934
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1979

def B1984 : Block := .branch 169 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 922).pointIds 922), (.leaf 2 (Common.fact 923).pointIds 923), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq1984 : B1984.tree = HexagonCover.NBand.M8500_8700.SplitData.node1984 := by
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

def B1983 : Block := .branch 170 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 920).pointIds 920), (.leaf 2 (Common.fact 921).pointIds 921), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1984, (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq1983 : B1983.tree = HexagonCover.NBand.M8500_8700.SplitData.node1983 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1984
  · rfl

def B1982 : Block := .branch 171 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 5986310706507378353287286997439407561319416980332552, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B1983]
theorem treeEq1982 : B1982.tree = HexagonCover.NBand.M8500_8700.SplitData.node1982 := by
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
  · exact treeEq1983

def B1981 : Block := .branch 172 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 916).pointIds 916), (.leaf 2 (Common.fact 917).pointIds 917), B1982, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq1981 : B1981.tree = HexagonCover.NBand.M8500_8700.SplitData.node1981 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1982
  · rfl
  · rfl
  · rfl

def B1932 : Block := .branch 113 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 324993922633512312808717284302856, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448] ![B1933, (.leaf 1 (Common.fact 300).pointIds 300), (.leaf 2 (Common.fact 301).pointIds 301), (.leaf 3 (Common.fact 302).pointIds 302), (.leaf 4 (Common.fact 303).pointIds 303), (.leaf 5 (Common.fact 304).pointIds 304), B1981]
theorem treeEq1932 : B1932.tree = HexagonCover.NBand.M8500_8700.SplitData.node1932 := by
  change Tree.branch (113 : Fin 175) _ = Tree.branch (113 : Fin 175) _
  apply congrArg (Tree.branch (113 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq1933
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1981

theorem accepted1932 : B1932.accepted = true := by decide +kernel
theorem checked1932 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node1932 (maskNeeds ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 324993922633512312808717284302856, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq1932]
  exact B1932.sound accepted1932
#print axioms checked1932

def Tip1931_1989 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node1989 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 475368975085586025561263726600, 1393800563241188408410454557028015476408336, 393248, 11226638389943763762426415598745871887892544] checked1989
def Tip1931_1932 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node1932 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 324993922633512312808717284302856, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448] checked1932
def B2026 : Block := .branch 171 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 5986310706507379017576607879913888757764604012027912, 1329227995784915872903807060280442896, 393248, 748288849507353694807469898273653799753954862039104] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 636).pointIds 636), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 692).pointIds 692)]
theorem treeEq2026 : B2026.tree = HexagonCover.NBand.M8500_8700.SplitData.node2026 := by
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

def B2025 : Block := .branch 172 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 664614314805107993509253904315998216, 1329227995784915872903807060280442896, 393248, 748288849507353694807469898273653799753954862039104] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 916).pointIds 916), (.leaf 2 (Common.fact 917).pointIds 917), B2026, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 691).pointIds 691)]
theorem treeEq2025 : B2025.tree = HexagonCover.NBand.M8500_8700.SplitData.node2025 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2026
  · rfl
  · rfl
  · rfl

def B2024 : Block := .branch 169 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 664614473261433022037929091403898888, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 11193931400687183263922916893690117400035392] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 922).pointIds 922), (.leaf 2 (Common.fact 923).pointIds 923), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), B2025]
theorem treeEq2024 : B2024.tree = HexagonCover.NBand.M8500_8700.SplitData.node2024 := by
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
  · exact treeEq2025

def B2023 : Block := .branch 170 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 664614473261433022037929091403898888, 1329227995784915872903807060280442896, 393248, 11193973941175345239765677444046542700281920] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 920).pointIds 920), (.leaf 2 (Common.fact 921).pointIds 921), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B2024, (.leaf 6 (Common.fact 690).pointIds 690)]
theorem treeEq2023 : B2023.tree = HexagonCover.NBand.M8500_8700.SplitData.node2023 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2024
  · rfl

def B1988 : Block := .branch 121 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 664614473261433022037929091403898888, 1393797904785196838578708749413894915719184, 393248, 11226638389943763762426415598745871887892544] ![(.leaf 0 (Common.fact 315).pointIds 315), (.leaf 1 (Common.fact 316).pointIds 316), (.leaf 2 (Common.fact 317).pointIds 317), (.leaf 3 (Common.fact 318).pointIds 318), Tip1931_1989, (.leaf 5 (Common.fact 319).pointIds 319), B2023]
theorem treeEq1988 : B1988.tree = HexagonCover.NBand.M8500_8700.SplitData.node1988 := by
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
  · exact treeEq2023

def B2031 : Block := .branch 169 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618506064983148595661900589669599936576] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 922).pointIds 922), (.leaf 2 (Common.fact 923).pointIds 923), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 688).pointIds 688)]
theorem treeEq2031 : B2031.tree = HexagonCover.NBand.M8500_8700.SplitData.node2031 := by
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

def B2030 : Block := .branch 170 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618506064983148595661900589669599936576] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 920).pointIds 920), (.leaf 2 (Common.fact 921).pointIds 921), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B2031, (.leaf 6 (Common.fact 686).pointIds 686)]
theorem treeEq2030 : B2030.tree = HexagonCover.NBand.M8500_8700.SplitData.node2030 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2031
  · rfl

def B2029 : Block := .branch 163 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1994491030784690662809276902461767696, 233840261972944466912589573234605283144949207269408, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 387).pointIds 387), B2030]
theorem treeEq2029 : B2029.tree = HexagonCover.NBand.M8500_8700.SplitData.node2029 := by
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
  · exact treeEq2030

def B2028 : Block := .branch 165 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1994491030784690662809276902461767696, 187072209578355573530071658587684226515959365894176, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 645).pointIds 645), B2029, (.leaf 0 [] 0)]
theorem treeEq2028 : B2028.tree = HexagonCover.NBand.M8500_8700.SplitData.node2028 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2029
  · rfl

def B2027 : Block := .branch 167 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1994491030784690662809276902461767696, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 644).pointIds 644), B2028, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq2027 : B2027.tree = HexagonCover.NBand.M8500_8700.SplitData.node2027 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2028
  · rfl

def B1987 : Block := .branch 119 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 475368975085586025561263726600, 1393797904785196838578708749413894915719184, 393248, 11226638389943763762426415598745871887892544] ![(.leaf 0 (Common.fact 310).pointIds 310), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), B1988, B2027, (.leaf 5 (Common.fact 313).pointIds 313), (.leaf 6 (Common.fact 314).pointIds 314)]
theorem treeEq1987 : B1987.tree = HexagonCover.NBand.M8500_8700.SplitData.node1987 := by
  change Tree.branch (119 : Fin 175) _ = Tree.branch (119 : Fin 175) _
  apply congrArg (Tree.branch (119 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1988
  · exact treeEq2027
  · rfl
  · rfl

def B2033 : Block := .branch 171 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 5986310706507378353287128541114379032644229892431880, 1329227995784915872903807060280442896, 393248, 11193971298296244245538414522023911127253056] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq2033 : B2033.tree = HexagonCover.NBand.M8500_8700.SplitData.node2033 := by
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

def B2032 : Block := .branch 172 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 324835466308483784133530196402184, 1329227995784915872903807060280442896, 393248, 11193971298296244245538414522023911127253056] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 916).pointIds 916), (.leaf 2 (Common.fact 917).pointIds 917), B2033, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 666).pointIds 666)]
theorem treeEq2032 : B2032.tree = HexagonCover.NBand.M8500_8700.SplitData.node2032 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2033
  · rfl
  · rfl
  · rfl

def B1986 : Block := .branch 114 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 324993922633512312808717284302856, 1393797904785196838578708749413894915719184, 393248, 11226638389943763762426415598745871887892544] ![B1987, (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 308).pointIds 308), (.leaf 5 (Common.fact 309).pointIds 309), B2032]
theorem treeEq1986 : B1986.tree = HexagonCover.NBand.M8500_8700.SplitData.node1986 := by
  change Tree.branch (114 : Fin 175) _ = Tree.branch (114 : Fin 175) _
  apply congrArg (Tree.branch (114 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq1987
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2032

def B2037 : Block := .branch 169 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 922).pointIds 922), (.leaf 2 (Common.fact 923).pointIds 923), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq2037 : B2037.tree = HexagonCover.NBand.M8500_8700.SplitData.node2037 := by
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

def B2036 : Block := .branch 170 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 920).pointIds 920), (.leaf 2 (Common.fact 921).pointIds 921), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B2037, (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq2036 : B2036.tree = HexagonCover.NBand.M8500_8700.SplitData.node2036 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2037
  · rfl

def B2035 : Block := .branch 171 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 5986310706507378353287286997439407561319416980332552, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B2036]
theorem treeEq2035 : B2035.tree = HexagonCover.NBand.M8500_8700.SplitData.node2035 := by
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
  · exact treeEq2036

def B2034 : Block := .branch 172 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 916).pointIds 916), (.leaf 2 (Common.fact 917).pointIds 917), B2035, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq2034 : B2034.tree = HexagonCover.NBand.M8500_8700.SplitData.node2034 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2035
  · rfl
  · rfl
  · rfl

def B1985 : Block := .branch 113 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 324993922633512312808717284302856, 1393797904785196838578708749413894915719184, 393248, 11226638389943763762426415598745871887892544] ![B1986, (.leaf 1 (Common.fact 300).pointIds 300), (.leaf 2 (Common.fact 301).pointIds 301), (.leaf 3 (Common.fact 302).pointIds 302), (.leaf 4 (Common.fact 303).pointIds 303), (.leaf 5 (Common.fact 304).pointIds 304), B2034]
theorem treeEq1985 : B1985.tree = HexagonCover.NBand.M8500_8700.SplitData.node1985 := by
  change Tree.branch (113 : Fin 175) _ = Tree.branch (113 : Fin 175) _
  apply congrArg (Tree.branch (113 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq1986
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2034

def B1931 : Block := .branch 112 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 324993922633512312808717284302856, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448] ![Tip1931_1932, (.leaf 1 (Common.fact 295).pointIds 295), (.leaf 2 (Common.fact 296).pointIds 296), (.leaf 3 (Common.fact 297).pointIds 297), (.leaf 4 (Common.fact 298).pointIds 298), (.leaf 5 (Common.fact 299).pointIds 299), B1985]
theorem treeEq1931 : B1931.tree = HexagonCover.NBand.M8500_8700.SplitData.node1931 := by
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
  · exact treeEq1985

theorem accepted1931 : B1931.accepted = true := by decide +kernel
theorem checked1931 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node1931 (maskNeeds ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 324993922633512312808717284302856, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq1931]
  exact B1931.sound accepted1931
#print axioms checked1931

end HexagonCover.NBand.M8500_8700.SplitTree.Run0027
