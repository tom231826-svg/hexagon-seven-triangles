import HexagonCover.NBand.M8500_8700.SplitData
import HexagonCover.NBand.M8500_8700.SplitTree.Run0014
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8500_8700.SplitTree.Run0015
open OwnerTree HexagonCover.NBand.M8500_8700

abbrev Block := Chunk (n := 175) (Certificate := Fin 1173) (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck

def B1150 : Block := .branch 169 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 3367299783604329065772481548669487163363265418362944] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 894).pointIds 894), (.leaf 2 (Common.fact 895).pointIds 895), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 444).pointIds 444)]
theorem treeEq1150 : B1150.tree = HexagonCover.NBand.M8500_8700.SplitData.node1150 := by
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

def B1149 : Block := .branch 170 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 3367299783604329065772481548669487163363265418362944] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 892).pointIds 892), (.leaf 2 (Common.fact 893).pointIds 893), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1150, (.leaf 6 (Common.fact 440).pointIds 440)]
theorem treeEq1149 : B1149.tree = HexagonCover.NBand.M8500_8700.SplitData.node1149 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1150
  · rfl

def B1148 : Block := .branch 171 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 5986310706855827496689809430367476432546391608287240, 1329227995784915872903807060280442896, 393248, 374144430350639889291335011266539539107915570348096] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 890).pointIds 890), (.leaf 2 (Common.fact 891).pointIds 891), (.leaf 3 (Common.fact 578).pointIds 578), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B1149]
theorem treeEq1148 : B1148.tree = HexagonCover.NBand.M8500_8700.SplitData.node1148 := by
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
  · exact treeEq1149

def B1147 : Block := .branch 172 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 393248, 374144430350639889291335011266539539107915570348096] ![(.leaf 0 (Common.fact 866).pointIds 866), (.leaf 1 (Common.fact 888).pointIds 888), (.leaf 2 (Common.fact 889).pointIds 889), B1148, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 452).pointIds 452)]
theorem treeEq1147 : B1147.tree = HexagonCover.NBand.M8500_8700.SplitData.node1147 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1148
  · rfl
  · rfl
  · rfl

def B1146 : Block := .branch 168 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 22300745198530623141535718272648361506373664, 11193928742231191694091171086075996839346240] ![(.leaf 0 (Common.fact 876).pointIds 876), (.leaf 1 (Common.fact 886).pointIds 886), (.leaf 2 (Common.fact 887).pointIds 887), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 517).pointIds 517), B1147]
theorem treeEq1146 : B1146.tree = HexagonCover.NBand.M8500_8700.SplitData.node1146 := by
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
  · exact treeEq1147

def B1152 : Block := .branch 171 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 5986310706855827496689650974042447903871204520386568, 1329227995784915872903807060280442896, 393248, 33451160338284096688146337959329517314506816] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 890).pointIds 890), (.leaf 2 (Common.fact 891).pointIds 891), (.leaf 3 (Common.fact 578).pointIds 578), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 684).pointIds 684)]
theorem treeEq1152 : B1152.tree = HexagonCover.NBand.M8500_8700.SplitData.node1152 := by
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

def B1151 : Block := .branch 172 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 348449143727357899236552655360504824356872, 1329227995784915872903807060280442896, 393248, 33451160338284096688146337959329517314506816] ![(.leaf 0 (Common.fact 866).pointIds 866), (.leaf 1 (Common.fact 888).pointIds 888), (.leaf 2 (Common.fact 889).pointIds 889), B1152, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 683).pointIds 683)]
theorem treeEq1151 : B1151.tree = HexagonCover.NBand.M8500_8700.SplitData.node1151 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1152
  · rfl
  · rfl
  · rfl

def B1145 : Block := .branch 144 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 340).pointIds 340), (.leaf 1 (Common.fact 341).pointIds 341), (.leaf 2 (Common.fact 342).pointIds 342), (.leaf 3 (Common.fact 343).pointIds 343), (.leaf 4 (Common.fact 344).pointIds 344), B1146, B1151]
theorem treeEq1145 : B1145.tree = HexagonCover.NBand.M8500_8700.SplitData.node1145 := by
  change Tree.branch (144 : Fin 175) _ = Tree.branch (144 : Fin 175) _
  apply congrArg (Tree.branch (144 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1146
  · exact treeEq1151

def B1158 : Block := .branch 169 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 3367299789179515365405137334053416731525355794858048] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 894).pointIds 894), (.leaf 2 (Common.fact 895).pointIds 895), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 586).pointIds 586)]
theorem treeEq1158 : B1158.tree = HexagonCover.NBand.M8500_8700.SplitData.node1158 := by
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

def B1157 : Block := .branch 170 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 3367299789179515365405137334053416731525355794858048] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 892).pointIds 892), (.leaf 2 (Common.fact 893).pointIds 893), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1158, (.leaf 6 (Common.fact 583).pointIds 583)]
theorem treeEq1157 : B1157.tree = HexagonCover.NBand.M8500_8700.SplitData.node1157 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1158
  · rfl

def B1156 : Block := .branch 171 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 5986310706855827496689809430367476432546391608287240, 1329227995784915872903807060280442896, 393248, 374144435925826188923990796650469107270005946843200] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 890).pointIds 890), (.leaf 2 (Common.fact 891).pointIds 891), (.leaf 3 (Common.fact 578).pointIds 578), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B1157]
theorem treeEq1156 : B1156.tree = HexagonCover.NBand.M8500_8700.SplitData.node1156 := by
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
  · exact treeEq1157

def B1155 : Block := .branch 172 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 393248, 374144435925826188923990796650469107270005946843200] ![(.leaf 0 (Common.fact 866).pointIds 866), (.leaf 1 (Common.fact 888).pointIds 888), (.leaf 2 (Common.fact 889).pointIds 889), B1156, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 577).pointIds 577)]
theorem treeEq1155 : B1155.tree = HexagonCover.NBand.M8500_8700.SplitData.node1155 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1156
  · rfl
  · rfl
  · rfl

def B1154 : Block := .branch 168 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 5708990770823839524233143877797980545531379744, 16769115041863847479475100654238087215841344] ![(.leaf 0 (Common.fact 876).pointIds 876), (.leaf 1 (Common.fact 886).pointIds 886), (.leaf 2 (Common.fact 887).pointIds 887), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 574).pointIds 574), B1155]
theorem treeEq1154 : B1154.tree = HexagonCover.NBand.M8500_8700.SplitData.node1154 := by
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
  · exact treeEq1155

def B1153 : Block := .branch 152 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 16769157582352009455317861204594512516087872] ![(.leaf 0 (Common.fact 354).pointIds 354), (.leaf 1 (Common.fact 355).pointIds 355), (.leaf 2 (Common.fact 356).pointIds 356), (.leaf 3 (Common.fact 357).pointIds 357), (.leaf 4 (Common.fact 358).pointIds 358), B1154, (.leaf 6 (Common.fact 685).pointIds 685)]
theorem treeEq1153 : B1153.tree = HexagonCover.NBand.M8500_8700.SplitData.node1153 := by
  change Tree.branch (152 : Fin 175) _ = Tree.branch (152 : Fin 175) _
  apply congrArg (Tree.branch (152 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1154
  · rfl

def B1144 : Block := .branch 142 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), B1145, (.leaf 5 (Common.fact 339).pointIds 339), B1153]
theorem treeEq1144 : B1144.tree = HexagonCover.NBand.M8500_8700.SplitData.node1144 := by
  change Tree.branch (142 : Fin 175) _ = Tree.branch (142 : Fin 175) _
  apply congrArg (Tree.branch (142 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1145
  · rfl
  · exact treeEq1153

theorem accepted1144 : B1144.accepted = true := by decide +kernel
theorem checked1144 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node1144 (maskNeeds ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 11193971282719353669933931636432422139592768]) := by
  rw [← treeEq1144]
  exact B1144.sound accepted1144
#print axioms checked1144

def Tip1141_1144 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node1144 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 11193971282719353669933931636432422139592768] checked1144
def B1163 : Block := .branch 169 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618506064983148595661900589669599936576] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 894).pointIds 894), (.leaf 2 (Common.fact 895).pointIds 895), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 688).pointIds 688)]
theorem treeEq1163 : B1163.tree = HexagonCover.NBand.M8500_8700.SplitData.node1163 := by
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

def B1162 : Block := .branch 170 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618506064983148595661900589669599936576] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 892).pointIds 892), (.leaf 2 (Common.fact 893).pointIds 893), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1163, (.leaf 6 (Common.fact 686).pointIds 686)]
theorem treeEq1162 : B1162.tree = HexagonCover.NBand.M8500_8700.SplitData.node1162 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1163
  · rfl

def B1161 : Block := .branch 163 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 353894991474808894234635949102411261509648, 233840261972944466912589573234605283144949207269408, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 589).pointIds 589), (.leaf 5 (Common.fact 387).pointIds 387), B1162]
theorem treeEq1161 : B1161.tree = HexagonCover.NBand.M8500_8700.SplitData.node1161 := by
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
  · exact treeEq1162

def B1160 : Block := .branch 165 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 353894991474808894234635949102411261509648, 187072209578355573530071658587684226515959365894176, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 588).pointIds 588), B1161, (.leaf 0 [] 0)]
theorem treeEq1160 : B1160.tree = HexagonCover.NBand.M8500_8700.SplitData.node1160 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1161
  · rfl

def B1159 : Block := .branch 167 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 353894991474808894234635949102411261509648, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 587).pointIds 587), B1160, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq1159 : B1159.tree = HexagonCover.NBand.M8500_8700.SplitData.node1159 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1160
  · rfl

def B1143 : Block := .branch 138 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 475368975085586025561263726600, 1399242422655931853994122743132803207102480, 393248, 11226638389943763762426415598745871887892544] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), Tip1141_1144, B1159, (.leaf 5 (Common.fact 333).pointIds 333), (.leaf 6 (Common.fact 334).pointIds 334)]
theorem treeEq1143 : B1143.tree = HexagonCover.NBand.M8500_8700.SplitData.node1143 := by
  change Tree.branch (138 : Fin 175) _ = Tree.branch (138 : Fin 175) _
  apply congrArg (Tree.branch (138 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1159
  · rfl
  · rfl

def B1169 : Block := .branch 169 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 3367299783609773583643216564084901157082173709746240] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 894).pointIds 894), (.leaf 2 (Common.fact 895).pointIds 895), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 615).pointIds 615)]
theorem treeEq1169 : B1169.tree = HexagonCover.NBand.M8500_8700.SplitData.node1169 := by
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

def B1168 : Block := .branch 170 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 3367299783609773583643216564084901157082173709746240] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 892).pointIds 892), (.leaf 2 (Common.fact 893).pointIds 893), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1169, (.leaf 6 (Common.fact 612).pointIds 612)]
theorem treeEq1168 : B1168.tree = HexagonCover.NBand.M8500_8700.SplitData.node1168 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1169
  · rfl

def B1167 : Block := .branch 171 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 5986310706508058917696610320707907583751124496179208, 1329227995784915872903807060280442896, 393248, 374144430356084407162070026681953532826823861731392] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 890).pointIds 890), (.leaf 2 (Common.fact 891).pointIds 891), (.leaf 3 (Common.fact 608).pointIds 608), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B1168]
theorem treeEq1167 : B1167.tree = HexagonCover.NBand.M8500_8700.SplitData.node1167 := by
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
  · exact treeEq1168

def B1166 : Block := .branch 172 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 680564734317245902012335240424800149512, 1329227995784915872903807060280442896, 393248, 374144430356084407162070026681953532826823861731392] ![(.leaf 0 (Common.fact 866).pointIds 866), (.leaf 1 (Common.fact 888).pointIds 888), (.leaf 2 (Common.fact 889).pointIds 889), B1167, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 607).pointIds 607)]
theorem treeEq1166 : B1166.tree = HexagonCover.NBand.M8500_8700.SplitData.node1166 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1167
  · rfl
  · rfl
  · rfl

def B1165 : Block := .branch 168 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 680564734317245902012335240424800149512, 1329227995784915872903807060280442896, 5708990770823839524233143877797980545531379744, 11199373260101926709506585079794905130729536] ![(.leaf 0 (Common.fact 876).pointIds 876), (.leaf 1 (Common.fact 886).pointIds 886), (.leaf 2 (Common.fact 887).pointIds 887), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 574).pointIds 574), B1166]
theorem treeEq1165 : B1165.tree = HexagonCover.NBand.M8500_8700.SplitData.node1165 := by
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
  · exact treeEq1166

def B1164 : Block := .branch 152 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 680564734317245902012335240424800149512, 1393797904136159731261855295847582874566672, 393248, 11199415800590088685349345630151330430976064] ![(.leaf 0 (Common.fact 354).pointIds 354), (.leaf 1 (Common.fact 355).pointIds 355), (.leaf 2 (Common.fact 356).pointIds 356), (.leaf 3 (Common.fact 357).pointIds 357), (.leaf 4 (Common.fact 358).pointIds 358), B1165, (.leaf 6 (Common.fact 689).pointIds 689)]
theorem treeEq1164 : B1164.tree = HexagonCover.NBand.M8500_8700.SplitData.node1164 := by
  change Tree.branch (152 : Fin 175) _ = Tree.branch (152 : Fin 175) _
  apply congrArg (Tree.branch (152 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1165
  · rfl

def B1142 : Block := .branch 132 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 680564734317245902012335240424800149512, 1393797904785196838578708749413894915719184, 393248, 11226638389943763762426415598745871887892544] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B1143, (.leaf 5 (Common.fact 329).pointIds 329), B1164]
theorem treeEq1142 : B1142.tree = HexagonCover.NBand.M8500_8700.SplitData.node1142 := by
  change Tree.branch (132 : Fin 175) _ = Tree.branch (132 : Fin 175) _
  apply congrArg (Tree.branch (132 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1143
  · rfl
  · exact treeEq1164

def B1174 : Block := .branch 169 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618506064983148595661900589669599936576] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 894).pointIds 894), (.leaf 2 (Common.fact 895).pointIds 895), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 688).pointIds 688)]
theorem treeEq1174 : B1174.tree = HexagonCover.NBand.M8500_8700.SplitData.node1174 := by
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

def B1173 : Block := .branch 170 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618506064983148595661900589669599936576] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 892).pointIds 892), (.leaf 2 (Common.fact 893).pointIds 893), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1174, (.leaf 6 (Common.fact 686).pointIds 686)]
theorem treeEq1173 : B1173.tree = HexagonCover.NBand.M8500_8700.SplitData.node1173 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1174
  · rfl

def B1172 : Block := .branch 163 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 684553066866338991398914202356418707472, 233840261972944466912589573234605283144949207269408, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 618).pointIds 618), (.leaf 5 (Common.fact 387).pointIds 387), B1173]
theorem treeEq1172 : B1172.tree = HexagonCover.NBand.M8500_8700.SplitData.node1172 := by
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
  · exact treeEq1173

def B1171 : Block := .branch 165 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 684553066866338991398914202356418707472, 187072209578355573530071658587684226515959365894176, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 617).pointIds 617), B1172, (.leaf 0 [] 0)]
theorem treeEq1171 : B1171.tree = HexagonCover.NBand.M8500_8700.SplitData.node1171 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1172
  · rfl

def B1170 : Block := .branch 167 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 684553066866338991398914202356418707472, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 616).pointIds 616), B1171, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq1170 : B1170.tree = HexagonCover.NBand.M8500_8700.SplitData.node1170 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1171
  · rfl

def B1141 : Block := .branch 129 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 475368975085586025561263726600, 1393800563241188408410454557028015476408336, 393248, 11226638389943763762426415598745871887892544] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), (.leaf 2 (Common.fact 322).pointIds 322), B1142, B1170, (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 6 (Common.fact 324).pointIds 324)]
theorem treeEq1141 : B1141.tree = HexagonCover.NBand.M8500_8700.SplitData.node1141 := by
  change Tree.branch (129 : Fin 175) _ = Tree.branch (129 : Fin 175) _
  apply congrArg (Tree.branch (129 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1142
  · exact treeEq1170
  · rfl
  · rfl

theorem accepted1141 : B1141.accepted = true := by decide +kernel
theorem checked1141 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node1141 (maskNeeds ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 475368975085586025561263726600, 1393800563241188408410454557028015476408336, 393248, 11226638389943763762426415598745871887892544]) := by
  rw [← treeEq1141]
  exact B1141.sound accepted1141
#print axioms checked1141

def Tip1084_1088 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node1088 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 475368975085586025561263726600, 1393800563241188408410454557028015476408336, 393248, 11226638384751466903891587970215375558672448] HexagonCover.NBand.M8500_8700.SplitTree.Run0014.checked1088
def B1125 : Block := .branch 171 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 5986310706507379017576607879913888757764604012027912, 1329227995784915872903807060280442896, 393248, 748288849507353694807469898273653799753954862039104] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 890).pointIds 890), (.leaf 2 (Common.fact 891).pointIds 891), (.leaf 3 (Common.fact 636).pointIds 636), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 692).pointIds 692)]
theorem treeEq1125 : B1125.tree = HexagonCover.NBand.M8500_8700.SplitData.node1125 := by
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

def B1124 : Block := .branch 172 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 664614314805107993509253904315998216, 1329227995784915872903807060280442896, 393248, 748288849507353694807469898273653799753954862039104] ![(.leaf 0 (Common.fact 866).pointIds 866), (.leaf 1 (Common.fact 888).pointIds 888), (.leaf 2 (Common.fact 889).pointIds 889), B1125, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 691).pointIds 691)]
theorem treeEq1124 : B1124.tree = HexagonCover.NBand.M8500_8700.SplitData.node1124 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1125
  · rfl
  · rfl
  · rfl

def B1123 : Block := .branch 169 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 664614473261433022037929091403898888, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 11193931400687183263922916893690117400035392] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 894).pointIds 894), (.leaf 2 (Common.fact 895).pointIds 895), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), B1124]
theorem treeEq1123 : B1123.tree = HexagonCover.NBand.M8500_8700.SplitData.node1123 := by
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
  · exact treeEq1124

def B1122 : Block := .branch 170 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 664614473261433022037929091403898888, 1329227995784915872903807060280442896, 393248, 11193973935983048381230849815516046371061824] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 892).pointIds 892), (.leaf 2 (Common.fact 893).pointIds 893), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1123, (.leaf 6 (Common.fact 643).pointIds 643)]
theorem treeEq1122 : B1122.tree = HexagonCover.NBand.M8500_8700.SplitData.node1122 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1123
  · rfl

def B1087 : Block := .branch 121 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 664614473261433022037929091403898888, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 315).pointIds 315), (.leaf 1 (Common.fact 316).pointIds 316), (.leaf 2 (Common.fact 317).pointIds 317), (.leaf 3 (Common.fact 318).pointIds 318), Tip1084_1088, (.leaf 5 (Common.fact 319).pointIds 319), B1122]
theorem treeEq1087 : B1087.tree = HexagonCover.NBand.M8500_8700.SplitData.node1087 := by
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
  · exact treeEq1122

def B1130 : Block := .branch 169 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 894).pointIds 894), (.leaf 2 (Common.fact 895).pointIds 895), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq1130 : B1130.tree = HexagonCover.NBand.M8500_8700.SplitData.node1130 := by
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

def B1129 : Block := .branch 170 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 892).pointIds 892), (.leaf 2 (Common.fact 893).pointIds 893), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1130, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq1129 : B1129.tree = HexagonCover.NBand.M8500_8700.SplitData.node1129 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1130
  · rfl

def B1128 : Block := .branch 163 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1994491030784690662809276902461767696, 233840261972944466912589573234605283144949207269408, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 387).pointIds 387), B1129]
theorem treeEq1128 : B1128.tree = HexagonCover.NBand.M8500_8700.SplitData.node1128 := by
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
  · exact treeEq1129

def B1127 : Block := .branch 165 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1994491030784690662809276902461767696, 187072209578355573530071658587684226515959365894176, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 645).pointIds 645), B1128, (.leaf 0 [] 0)]
theorem treeEq1127 : B1127.tree = HexagonCover.NBand.M8500_8700.SplitData.node1127 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1128
  · rfl

def B1126 : Block := .branch 167 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1994491030784690662809276902461767696, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 644).pointIds 644), B1127, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq1126 : B1126.tree = HexagonCover.NBand.M8500_8700.SplitData.node1126 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1127
  · rfl

def B1086 : Block := .branch 119 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 475368975085586025561263726600, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 310).pointIds 310), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), B1087, B1126, (.leaf 5 (Common.fact 313).pointIds 313), (.leaf 6 (Common.fact 314).pointIds 314)]
theorem treeEq1086 : B1086.tree = HexagonCover.NBand.M8500_8700.SplitData.node1086 := by
  change Tree.branch (119 : Fin 175) _ = Tree.branch (119 : Fin 175) _
  apply congrArg (Tree.branch (119 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1087
  · exact treeEq1126
  · rfl
  · rfl

def B1132 : Block := .branch 171 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 5986310706507378353287128541114379032644229892431880, 1329227995784915872903807060280442896, 393248, 11193971298296244245538414522023911127253056] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 890).pointIds 890), (.leaf 2 (Common.fact 891).pointIds 891), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq1132 : B1132.tree = HexagonCover.NBand.M8500_8700.SplitData.node1132 := by
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

def B1131 : Block := .branch 172 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 324835466308483784133530196402184, 1329227995784915872903807060280442896, 393248, 11193971298296244245538414522023911127253056] ![(.leaf 0 (Common.fact 866).pointIds 866), (.leaf 1 (Common.fact 888).pointIds 888), (.leaf 2 (Common.fact 889).pointIds 889), B1132, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 666).pointIds 666)]
theorem treeEq1131 : B1131.tree = HexagonCover.NBand.M8500_8700.SplitData.node1131 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1132
  · rfl
  · rfl
  · rfl

def B1085 : Block := .branch 114 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 324993922633512312808717284302856, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448] ![B1086, (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 308).pointIds 308), (.leaf 5 (Common.fact 309).pointIds 309), B1131]
theorem treeEq1085 : B1085.tree = HexagonCover.NBand.M8500_8700.SplitData.node1085 := by
  change Tree.branch (114 : Fin 175) _ = Tree.branch (114 : Fin 175) _
  apply congrArg (Tree.branch (114 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq1086
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1131

def B1136 : Block := .branch 169 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 894).pointIds 894), (.leaf 2 (Common.fact 895).pointIds 895), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq1136 : B1136.tree = HexagonCover.NBand.M8500_8700.SplitData.node1136 := by
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

def B1135 : Block := .branch 170 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 892).pointIds 892), (.leaf 2 (Common.fact 893).pointIds 893), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1136, (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq1135 : B1135.tree = HexagonCover.NBand.M8500_8700.SplitData.node1135 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1136
  · rfl

def B1134 : Block := .branch 171 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 5986310706507378353287286997439407561319416980332552, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 890).pointIds 890), (.leaf 2 (Common.fact 891).pointIds 891), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B1135]
theorem treeEq1134 : B1134.tree = HexagonCover.NBand.M8500_8700.SplitData.node1134 := by
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
  · exact treeEq1135

def B1133 : Block := .branch 172 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 866).pointIds 866), (.leaf 1 (Common.fact 888).pointIds 888), (.leaf 2 (Common.fact 889).pointIds 889), B1134, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq1133 : B1133.tree = HexagonCover.NBand.M8500_8700.SplitData.node1133 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1134
  · rfl
  · rfl
  · rfl

def B1084 : Block := .branch 113 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 324993922633512312808717284302856, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448] ![B1085, (.leaf 1 (Common.fact 300).pointIds 300), (.leaf 2 (Common.fact 301).pointIds 301), (.leaf 3 (Common.fact 302).pointIds 302), (.leaf 4 (Common.fact 303).pointIds 303), (.leaf 5 (Common.fact 304).pointIds 304), B1133]
theorem treeEq1084 : B1084.tree = HexagonCover.NBand.M8500_8700.SplitData.node1084 := by
  change Tree.branch (113 : Fin 175) _ = Tree.branch (113 : Fin 175) _
  apply congrArg (Tree.branch (113 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq1085
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1133

theorem accepted1084 : B1084.accepted = true := by decide +kernel
theorem checked1084 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node1084 (maskNeeds ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 324993922633512312808717284302856, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq1084]
  exact B1084.sound accepted1084
#print axioms checked1084

def Tip1083_1141 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node1141 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 475368975085586025561263726600, 1393800563241188408410454557028015476408336, 393248, 11226638389943763762426415598745871887892544] checked1141
def Tip1083_1084 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node1084 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 324993922633512312808717284302856, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448] checked1084
def B1178 : Block := .branch 171 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 5986310706507379017576607879913888757764604012027912, 1329227995784915872903807060280442896, 393248, 748288849507353694807469898273653799753954862039104] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 890).pointIds 890), (.leaf 2 (Common.fact 891).pointIds 891), (.leaf 3 (Common.fact 636).pointIds 636), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 692).pointIds 692)]
theorem treeEq1178 : B1178.tree = HexagonCover.NBand.M8500_8700.SplitData.node1178 := by
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

def B1177 : Block := .branch 172 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 664614314805107993509253904315998216, 1329227995784915872903807060280442896, 393248, 748288849507353694807469898273653799753954862039104] ![(.leaf 0 (Common.fact 866).pointIds 866), (.leaf 1 (Common.fact 888).pointIds 888), (.leaf 2 (Common.fact 889).pointIds 889), B1178, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 691).pointIds 691)]
theorem treeEq1177 : B1177.tree = HexagonCover.NBand.M8500_8700.SplitData.node1177 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1178
  · rfl
  · rfl
  · rfl

def B1176 : Block := .branch 169 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 664614473261433022037929091403898888, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 11193931400687183263922916893690117400035392] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 894).pointIds 894), (.leaf 2 (Common.fact 895).pointIds 895), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), B1177]
theorem treeEq1176 : B1176.tree = HexagonCover.NBand.M8500_8700.SplitData.node1176 := by
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
  · exact treeEq1177

def B1175 : Block := .branch 170 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 664614473261433022037929091403898888, 1329227995784915872903807060280442896, 393248, 11193973941175345239765677444046542700281920] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 892).pointIds 892), (.leaf 2 (Common.fact 893).pointIds 893), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1176, (.leaf 6 (Common.fact 690).pointIds 690)]
theorem treeEq1175 : B1175.tree = HexagonCover.NBand.M8500_8700.SplitData.node1175 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1176
  · rfl

def B1140 : Block := .branch 121 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 664614473261433022037929091403898888, 1393797904785196838578708749413894915719184, 393248, 11226638389943763762426415598745871887892544] ![(.leaf 0 (Common.fact 315).pointIds 315), (.leaf 1 (Common.fact 316).pointIds 316), (.leaf 2 (Common.fact 317).pointIds 317), (.leaf 3 (Common.fact 318).pointIds 318), Tip1083_1141, (.leaf 5 (Common.fact 319).pointIds 319), B1175]
theorem treeEq1140 : B1140.tree = HexagonCover.NBand.M8500_8700.SplitData.node1140 := by
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
  · exact treeEq1175

def B1183 : Block := .branch 169 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618506064983148595661900589669599936576] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 894).pointIds 894), (.leaf 2 (Common.fact 895).pointIds 895), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 688).pointIds 688)]
theorem treeEq1183 : B1183.tree = HexagonCover.NBand.M8500_8700.SplitData.node1183 := by
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

def B1182 : Block := .branch 170 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618506064983148595661900589669599936576] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 892).pointIds 892), (.leaf 2 (Common.fact 893).pointIds 893), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1183, (.leaf 6 (Common.fact 686).pointIds 686)]
theorem treeEq1182 : B1182.tree = HexagonCover.NBand.M8500_8700.SplitData.node1182 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1183
  · rfl

def B1181 : Block := .branch 163 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1994491030784690662809276902461767696, 233840261972944466912589573234605283144949207269408, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 387).pointIds 387), B1182]
theorem treeEq1181 : B1181.tree = HexagonCover.NBand.M8500_8700.SplitData.node1181 := by
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
  · exact treeEq1182

def B1180 : Block := .branch 165 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1994491030784690662809276902461767696, 187072209578355573530071658587684226515959365894176, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 645).pointIds 645), B1181, (.leaf 0 [] 0)]
theorem treeEq1180 : B1180.tree = HexagonCover.NBand.M8500_8700.SplitData.node1180 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1181
  · rfl

def B1179 : Block := .branch 167 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1994491030784690662809276902461767696, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 644).pointIds 644), B1180, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq1179 : B1179.tree = HexagonCover.NBand.M8500_8700.SplitData.node1179 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1180
  · rfl

def B1139 : Block := .branch 119 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 475368975085586025561263726600, 1393797904785196838578708749413894915719184, 393248, 11226638389943763762426415598745871887892544] ![(.leaf 0 (Common.fact 310).pointIds 310), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), B1140, B1179, (.leaf 5 (Common.fact 313).pointIds 313), (.leaf 6 (Common.fact 314).pointIds 314)]
theorem treeEq1139 : B1139.tree = HexagonCover.NBand.M8500_8700.SplitData.node1139 := by
  change Tree.branch (119 : Fin 175) _ = Tree.branch (119 : Fin 175) _
  apply congrArg (Tree.branch (119 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1140
  · exact treeEq1179
  · rfl
  · rfl

def B1185 : Block := .branch 171 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 5986310706507378353287128541114379032644229892431880, 1329227995784915872903807060280442896, 393248, 11193971298296244245538414522023911127253056] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 890).pointIds 890), (.leaf 2 (Common.fact 891).pointIds 891), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq1185 : B1185.tree = HexagonCover.NBand.M8500_8700.SplitData.node1185 := by
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

def B1184 : Block := .branch 172 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 324835466308483784133530196402184, 1329227995784915872903807060280442896, 393248, 11193971298296244245538414522023911127253056] ![(.leaf 0 (Common.fact 866).pointIds 866), (.leaf 1 (Common.fact 888).pointIds 888), (.leaf 2 (Common.fact 889).pointIds 889), B1185, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 666).pointIds 666)]
theorem treeEq1184 : B1184.tree = HexagonCover.NBand.M8500_8700.SplitData.node1184 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1185
  · rfl
  · rfl
  · rfl

def B1138 : Block := .branch 114 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 324993922633512312808717284302856, 1393797904785196838578708749413894915719184, 393248, 11226638389943763762426415598745871887892544] ![B1139, (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 308).pointIds 308), (.leaf 5 (Common.fact 309).pointIds 309), B1184]
theorem treeEq1138 : B1138.tree = HexagonCover.NBand.M8500_8700.SplitData.node1138 := by
  change Tree.branch (114 : Fin 175) _ = Tree.branch (114 : Fin 175) _
  apply congrArg (Tree.branch (114 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq1139
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1184

def B1189 : Block := .branch 169 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 894).pointIds 894), (.leaf 2 (Common.fact 895).pointIds 895), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq1189 : B1189.tree = HexagonCover.NBand.M8500_8700.SplitData.node1189 := by
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

def B1188 : Block := .branch 170 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 892).pointIds 892), (.leaf 2 (Common.fact 893).pointIds 893), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1189, (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq1188 : B1188.tree = HexagonCover.NBand.M8500_8700.SplitData.node1188 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1189
  · rfl

def B1187 : Block := .branch 171 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 5986310706507378353287286997439407561319416980332552, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 890).pointIds 890), (.leaf 2 (Common.fact 891).pointIds 891), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B1188]
theorem treeEq1187 : B1187.tree = HexagonCover.NBand.M8500_8700.SplitData.node1187 := by
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
  · exact treeEq1188

def B1186 : Block := .branch 172 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 866).pointIds 866), (.leaf 1 (Common.fact 888).pointIds 888), (.leaf 2 (Common.fact 889).pointIds 889), B1187, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq1186 : B1186.tree = HexagonCover.NBand.M8500_8700.SplitData.node1186 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1187
  · rfl
  · rfl
  · rfl

def B1137 : Block := .branch 113 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 324993922633512312808717284302856, 1393797904785196838578708749413894915719184, 393248, 11226638389943763762426415598745871887892544] ![B1138, (.leaf 1 (Common.fact 300).pointIds 300), (.leaf 2 (Common.fact 301).pointIds 301), (.leaf 3 (Common.fact 302).pointIds 302), (.leaf 4 (Common.fact 303).pointIds 303), (.leaf 5 (Common.fact 304).pointIds 304), B1186]
theorem treeEq1137 : B1137.tree = HexagonCover.NBand.M8500_8700.SplitData.node1137 := by
  change Tree.branch (113 : Fin 175) _ = Tree.branch (113 : Fin 175) _
  apply congrArg (Tree.branch (113 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq1138
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1186

def B1083 : Block := .branch 112 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 324993922633512312808717284302856, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448] ![Tip1083_1084, (.leaf 1 (Common.fact 295).pointIds 295), (.leaf 2 (Common.fact 296).pointIds 296), (.leaf 3 (Common.fact 297).pointIds 297), (.leaf 4 (Common.fact 298).pointIds 298), (.leaf 5 (Common.fact 299).pointIds 299), B1137]
theorem treeEq1083 : B1083.tree = HexagonCover.NBand.M8500_8700.SplitData.node1083 := by
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
  · exact treeEq1137

theorem accepted1083 : B1083.accepted = true := by decide +kernel
theorem checked1083 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node1083 (maskNeeds ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 324993922633512312808717284302856, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq1083]
  exact B1083.sound accepted1083
#print axioms checked1083

end HexagonCover.NBand.M8500_8700.SplitTree.Run0015
