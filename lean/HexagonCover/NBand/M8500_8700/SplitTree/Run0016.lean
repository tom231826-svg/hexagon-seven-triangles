import HexagonCover.NBand.M8500_8700.SplitData
import HexagonCover.NBand.M8500_8700.SplitTree.Run0015
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8500_8700.SplitTree.Run0016
open OwnerTree HexagonCover.NBand.M8500_8700

abbrev Block := Chunk (n := 175) (Certificate := Fin 1173) (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck

def Tip1079_1083 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node1083 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 324993922633512312808717284302856, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448] HexagonCover.NBand.M8500_8700.SplitTree.Run0015.checked1083
def B1191 : Block := .branch 168 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 11193971278176093918715957461468237851525184] ![(.leaf 0 (Common.fact 876).pointIds 876), (.leaf 1 (Common.fact 886).pointIds 886), (.leaf 2 (Common.fact 887).pointIds 887), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 765).pointIds 765), (.leaf 6 (Common.fact 706).pointIds 706)]
theorem treeEq1191 : B1191.tree = HexagonCover.NBand.M8500_8700.SplitData.node1191 := by
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

def B1190 : Block := .branch 170 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 11193971278176093918715957461468237851525184] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 892).pointIds 892), (.leaf 2 (Common.fact 893).pointIds 893), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1191, (.leaf 6 (Common.fact 760).pointIds 760)]
theorem treeEq1190 : B1190.tree = HexagonCover.NBand.M8500_8700.SplitData.node1190 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1191
  · rfl

def B1082 : Block := .branch 109 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 325073150796026577146310828253192, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 290).pointIds 290), (.leaf 1 (Common.fact 291).pointIds 291), (.leaf 2 (Common.fact 292).pointIds 292), (.leaf 3 (Common.fact 293).pointIds 293), Tip1079_1083, (.leaf 5 (Common.fact 294).pointIds 294), B1190]
theorem treeEq1082 : B1082.tree = HexagonCover.NBand.M8500_8700.SplitData.node1082 := by
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
  · exact treeEq1190

def B1196 : Block := .branch 169 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 894).pointIds 894), (.leaf 2 (Common.fact 895).pointIds 895), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq1196 : B1196.tree = HexagonCover.NBand.M8500_8700.SplitData.node1196 := by
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

def B1195 : Block := .branch 170 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 892).pointIds 892), (.leaf 2 (Common.fact 893).pointIds 893), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1196, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq1195 : B1195.tree = HexagonCover.NBand.M8500_8700.SplitData.node1195 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1196
  · rfl

def B1194 : Block := .branch 163 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329552514338574299630590216301019152, 233840261972944466912589573234605283144949207269408, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 709).pointIds 709), (.leaf 5 (Common.fact 387).pointIds 387), B1195]
theorem treeEq1194 : B1194.tree = HexagonCover.NBand.M8500_8700.SplitData.node1194 := by
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
  · exact treeEq1195

def B1193 : Block := .branch 165 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329552514338574299630590216301019152, 187072209578355573530071658587684226515959365894176, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 708).pointIds 708), B1194, (.leaf 0 [] 0)]
theorem treeEq1193 : B1193.tree = HexagonCover.NBand.M8500_8700.SplitData.node1193 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1194
  · rfl

def B1192 : Block := .branch 167 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329552514338574299630590216301019152, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 707).pointIds 707), B1193, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq1192 : B1192.tree = HexagonCover.NBand.M8500_8700.SplitData.node1192 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1193
  · rfl

def B1081 : Block := .branch 108 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 554597137599850363154807676936, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), B1082, B1192, (.leaf 5 (Common.fact 288).pointIds 288), (.leaf 6 (Common.fact 289).pointIds 289)]
theorem treeEq1081 : B1081.tree = HexagonCover.NBand.M8500_8700.SplitData.node1081 := by
  change Tree.branch (108 : Fin 175) _ = Tree.branch (108 : Fin 175) _
  apply congrArg (Tree.branch (108 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1082
  · exact treeEq1192
  · rfl
  · rfl

def B1198 : Block := .branch 171 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 5986310706507378352962609987455952305861073871855624, 1329227995784915872903807060280442896, 393248, 11193971277528324461999332237303422513578048] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 890).pointIds 890), (.leaf 2 (Common.fact 891).pointIds 891), (.leaf 3 (Common.fact 766).pointIds 766), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 726).pointIds 726)]
theorem treeEq1198 : B1198.tree = HexagonCover.NBand.M8500_8700.SplitData.node1198 := by
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

def B1197 : Block := .branch 172 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 316912650057057350374175825928, 1329227995784915872903807060280442896, 393248, 11193971277528324461999332237303422513578048] ![(.leaf 0 (Common.fact 866).pointIds 866), (.leaf 1 (Common.fact 888).pointIds 888), (.leaf 2 (Common.fact 889).pointIds 889), B1198, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 728).pointIds 728)]
theorem treeEq1197 : B1197.tree = HexagonCover.NBand.M8500_8700.SplitData.node1197 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1198
  · rfl
  · rfl
  · rfl

def B1080 : Block := .branch 100 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 554597137599850363154807676936, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448] ![B1081, (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 281).pointIds 281), (.leaf 3 (Common.fact 282).pointIds 282), (.leaf 4 (Common.fact 283).pointIds 283), (.leaf 5 (Common.fact 284).pointIds 284), B1197]
theorem treeEq1080 : B1080.tree = HexagonCover.NBand.M8500_8700.SplitData.node1080 := by
  change Tree.branch (100 : Fin 175) _ = Tree.branch (100 : Fin 175) _
  apply congrArg (Tree.branch (100 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq1081
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1197

def B1203 : Block := .branch 169 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 894).pointIds 894), (.leaf 2 (Common.fact 895).pointIds 895), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq1203 : B1203.tree = HexagonCover.NBand.M8500_8700.SplitData.node1203 := by
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

def B1202 : Block := .branch 170 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 892).pointIds 892), (.leaf 2 (Common.fact 893).pointIds 893), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1203, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq1202 : B1202.tree = HexagonCover.NBand.M8500_8700.SplitData.node1202 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1203
  · rfl

def B1201 : Block := .branch 163 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329228312697565929961157434456244240, 233840261972944466912589573234605283144949207269408, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 731).pointIds 731), (.leaf 5 (Common.fact 387).pointIds 387), B1202]
theorem treeEq1201 : B1201.tree = HexagonCover.NBand.M8500_8700.SplitData.node1201 := by
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
  · exact treeEq1202

def B1200 : Block := .branch 165 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329228312697565929961157434456244240, 187072209578355573530071658587684226515959365894176, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 730).pointIds 730), B1201, (.leaf 0 [] 0)]
theorem treeEq1200 : B1200.tree = HexagonCover.NBand.M8500_8700.SplitData.node1200 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1201
  · rfl

def B1199 : Block := .branch 167 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329228312697565929961157434456244240, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 729).pointIds 729), B1200, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq1199 : B1199.tree = HexagonCover.NBand.M8500_8700.SplitData.node1199 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1200
  · rfl

def B1079 : Block := .branch 98 ![1237940335011998006369059201, 151152620940525821756930, 75576310469988032976900, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 275).pointIds 275), (.leaf 1 (Common.fact 276).pointIds 276), (.leaf 2 (Common.fact 277).pointIds 277), B1080, B1199, (.leaf 5 (Common.fact 278).pointIds 278), (.leaf 6 (Common.fact 279).pointIds 279)]
theorem treeEq1079 : B1079.tree = HexagonCover.NBand.M8500_8700.SplitData.node1079 := by
  change Tree.branch (98 : Fin 175) _ = Tree.branch (98 : Fin 175) _
  apply congrArg (Tree.branch (98 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1080
  · exact treeEq1199
  · rfl
  · rfl

theorem accepted1079 : B1079.accepted = true := by decide +kernel
theorem checked1079 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node1079 (maskNeeds ![1237940335011998006369059201, 151152620940525821756930, 75576310469988032976900, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq1079]
  exact B1079.sound accepted1079
#print axioms checked1079

def B1226 : Block := .branch 169 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 3367299783604329065772481548669487163363265418362944] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 894).pointIds 894), (.leaf 2 (Common.fact 895).pointIds 895), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 444).pointIds 444)]
theorem treeEq1226 : B1226.tree = HexagonCover.NBand.M8500_8700.SplitData.node1226 := by
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

def B1225 : Block := .branch 170 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 3367299783604329065772481548669487163363265418362944] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 892).pointIds 892), (.leaf 2 (Common.fact 893).pointIds 893), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1226, (.leaf 6 (Common.fact 440).pointIds 440)]
theorem treeEq1225 : B1225.tree = HexagonCover.NBand.M8500_8700.SplitData.node1225 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1226
  · rfl

def B1224 : Block := .branch 171 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 5986310706855827496689809430367476432546391608287240, 1329227995784915872903807060280442896, 393248, 374144430350639889291335011266539539107915570348096] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 890).pointIds 890), (.leaf 2 (Common.fact 891).pointIds 891), (.leaf 3 (Common.fact 578).pointIds 578), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B1225]
theorem treeEq1224 : B1224.tree = HexagonCover.NBand.M8500_8700.SplitData.node1224 := by
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
  · exact treeEq1225

def B1223 : Block := .branch 172 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 393248, 374144430350639889291335011266539539107915570348096] ![(.leaf 0 (Common.fact 866).pointIds 866), (.leaf 1 (Common.fact 888).pointIds 888), (.leaf 2 (Common.fact 889).pointIds 889), B1224, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 452).pointIds 452)]
theorem treeEq1223 : B1223.tree = HexagonCover.NBand.M8500_8700.SplitData.node1223 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1224
  · rfl
  · rfl
  · rfl

def B1222 : Block := .branch 168 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 22300745198530623141535718272648361506373664, 11193928742231191694091171086075996839346240] ![(.leaf 0 (Common.fact 876).pointIds 876), (.leaf 1 (Common.fact 886).pointIds 886), (.leaf 2 (Common.fact 887).pointIds 887), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 517).pointIds 517), B1223]
theorem treeEq1222 : B1222.tree = HexagonCover.NBand.M8500_8700.SplitData.node1222 := by
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
  · exact treeEq1223

def B1228 : Block := .branch 171 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 5986310706855827496689650974042447903871204520386568, 1329227995784915872903807060280442896, 393248, 33451160333091799829611510330799020985286720] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 890).pointIds 890), (.leaf 2 (Common.fact 891).pointIds 891), (.leaf 3 (Common.fact 578).pointIds 578), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 567).pointIds 567)]
theorem treeEq1228 : B1228.tree = HexagonCover.NBand.M8500_8700.SplitData.node1228 := by
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

def B1227 : Block := .branch 172 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 348449143727357899236552655360504824356872, 1329227995784915872903807060280442896, 393248, 33451160333091799829611510330799020985286720] ![(.leaf 0 (Common.fact 866).pointIds 866), (.leaf 1 (Common.fact 888).pointIds 888), (.leaf 2 (Common.fact 889).pointIds 889), B1228, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 570).pointIds 570)]
theorem treeEq1227 : B1227.tree = HexagonCover.NBand.M8500_8700.SplitData.node1227 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1228
  · rfl
  · rfl
  · rfl

def B1221 : Block := .branch 144 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 340).pointIds 340), (.leaf 1 (Common.fact 341).pointIds 341), (.leaf 2 (Common.fact 342).pointIds 342), (.leaf 3 (Common.fact 343).pointIds 343), (.leaf 4 (Common.fact 344).pointIds 344), B1222, B1227]
theorem treeEq1221 : B1221.tree = HexagonCover.NBand.M8500_8700.SplitData.node1221 := by
  change Tree.branch (144 : Fin 175) _ = Tree.branch (144 : Fin 175) _
  apply congrArg (Tree.branch (144 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1222
  · exact treeEq1227

def B1234 : Block := .branch 169 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 3367299789179515365405137334053416731525355794858048] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 894).pointIds 894), (.leaf 2 (Common.fact 895).pointIds 895), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 586).pointIds 586)]
theorem treeEq1234 : B1234.tree = HexagonCover.NBand.M8500_8700.SplitData.node1234 := by
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

def B1233 : Block := .branch 170 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 3367299789179515365405137334053416731525355794858048] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 892).pointIds 892), (.leaf 2 (Common.fact 893).pointIds 893), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1234, (.leaf 6 (Common.fact 583).pointIds 583)]
theorem treeEq1233 : B1233.tree = HexagonCover.NBand.M8500_8700.SplitData.node1233 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1234
  · rfl

def B1232 : Block := .branch 171 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 5986310706855827496689809430367476432546391608287240, 1329227995784915872903807060280442896, 393248, 374144435925826188923990796650469107270005946843200] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 890).pointIds 890), (.leaf 2 (Common.fact 891).pointIds 891), (.leaf 3 (Common.fact 578).pointIds 578), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B1233]
theorem treeEq1232 : B1232.tree = HexagonCover.NBand.M8500_8700.SplitData.node1232 := by
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
  · exact treeEq1233

def B1231 : Block := .branch 172 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 393248, 374144435925826188923990796650469107270005946843200] ![(.leaf 0 (Common.fact 866).pointIds 866), (.leaf 1 (Common.fact 888).pointIds 888), (.leaf 2 (Common.fact 889).pointIds 889), B1232, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 577).pointIds 577)]
theorem treeEq1231 : B1231.tree = HexagonCover.NBand.M8500_8700.SplitData.node1231 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1232
  · rfl
  · rfl
  · rfl

def B1230 : Block := .branch 168 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 5708990770823839524233143877797980545531379744, 16769115041863847479475100654238087215841344] ![(.leaf 0 (Common.fact 876).pointIds 876), (.leaf 1 (Common.fact 886).pointIds 886), (.leaf 2 (Common.fact 887).pointIds 887), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 574).pointIds 574), B1231]
theorem treeEq1230 : B1230.tree = HexagonCover.NBand.M8500_8700.SplitData.node1230 := by
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
  · exact treeEq1231

def B1229 : Block := .branch 152 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 16769157577159712596783033576064016186867776] ![(.leaf 0 (Common.fact 354).pointIds 354), (.leaf 1 (Common.fact 355).pointIds 355), (.leaf 2 (Common.fact 356).pointIds 356), (.leaf 3 (Common.fact 357).pointIds 357), (.leaf 4 (Common.fact 358).pointIds 358), B1230, (.leaf 6 (Common.fact 571).pointIds 571)]
theorem treeEq1229 : B1229.tree = HexagonCover.NBand.M8500_8700.SplitData.node1229 := by
  change Tree.branch (152 : Fin 175) _ = Tree.branch (152 : Fin 175) _
  apply congrArg (Tree.branch (152 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1230
  · rfl

def B1220 : Block := .branch 142 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), B1221, (.leaf 5 (Common.fact 339).pointIds 339), B1229]
theorem treeEq1220 : B1220.tree = HexagonCover.NBand.M8500_8700.SplitData.node1220 := by
  change Tree.branch (142 : Fin 175) _ = Tree.branch (142 : Fin 175) _
  apply congrArg (Tree.branch (142 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1221
  · rfl
  · exact treeEq1229

theorem accepted1220 : B1220.accepted = true := by decide +kernel
theorem checked1220 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node1220 (maskNeeds ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 11193971277527056811399104007901925810372672]) := by
  rw [← treeEq1220]
  exact B1220.sound accepted1220
#print axioms checked1220

def Tip1217_1220 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node1220 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 11193971277527056811399104007901925810372672] checked1220
def B1239 : Block := .branch 169 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 894).pointIds 894), (.leaf 2 (Common.fact 895).pointIds 895), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq1239 : B1239.tree = HexagonCover.NBand.M8500_8700.SplitData.node1239 := by
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

def B1238 : Block := .branch 170 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 892).pointIds 892), (.leaf 2 (Common.fact 893).pointIds 893), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1239, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq1238 : B1238.tree = HexagonCover.NBand.M8500_8700.SplitData.node1238 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1239
  · rfl

def B1237 : Block := .branch 163 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 353894991474808894234635949102411261509648, 233840261972944466912589573234605283144949207269408, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 589).pointIds 589), (.leaf 5 (Common.fact 387).pointIds 387), B1238]
theorem treeEq1237 : B1237.tree = HexagonCover.NBand.M8500_8700.SplitData.node1237 := by
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
  · exact treeEq1238

def B1236 : Block := .branch 165 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 353894991474808894234635949102411261509648, 187072209578355573530071658587684226515959365894176, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 588).pointIds 588), B1237, (.leaf 0 [] 0)]
theorem treeEq1236 : B1236.tree = HexagonCover.NBand.M8500_8700.SplitData.node1236 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1237
  · rfl

def B1235 : Block := .branch 167 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 353894991474808894234635949102411261509648, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 587).pointIds 587), B1236, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq1235 : B1235.tree = HexagonCover.NBand.M8500_8700.SplitData.node1235 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1236
  · rfl

def B1219 : Block := .branch 138 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 475368975085586025561263726600, 1399242422655931853994122743132803207102480, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), Tip1217_1220, B1235, (.leaf 5 (Common.fact 333).pointIds 333), (.leaf 6 (Common.fact 334).pointIds 334)]
theorem treeEq1219 : B1219.tree = HexagonCover.NBand.M8500_8700.SplitData.node1219 := by
  change Tree.branch (138 : Fin 175) _ = Tree.branch (138 : Fin 175) _
  apply congrArg (Tree.branch (138 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1235
  · rfl
  · rfl

def B1245 : Block := .branch 169 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 3367299783609773583643216564084901157082173709746240] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 894).pointIds 894), (.leaf 2 (Common.fact 895).pointIds 895), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 615).pointIds 615)]
theorem treeEq1245 : B1245.tree = HexagonCover.NBand.M8500_8700.SplitData.node1245 := by
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

def B1244 : Block := .branch 170 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 3367299783609773583643216564084901157082173709746240] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 892).pointIds 892), (.leaf 2 (Common.fact 893).pointIds 893), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1245, (.leaf 6 (Common.fact 612).pointIds 612)]
theorem treeEq1244 : B1244.tree = HexagonCover.NBand.M8500_8700.SplitData.node1244 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1245
  · rfl

def B1243 : Block := .branch 171 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 5986310706508058917696610320707907583751124496179208, 1329227995784915872903807060280442896, 393248, 374144430356084407162070026681953532826823861731392] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 890).pointIds 890), (.leaf 2 (Common.fact 891).pointIds 891), (.leaf 3 (Common.fact 608).pointIds 608), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B1244]
theorem treeEq1243 : B1243.tree = HexagonCover.NBand.M8500_8700.SplitData.node1243 := by
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
  · exact treeEq1244

def B1242 : Block := .branch 172 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 680564734317245902012335240424800149512, 1329227995784915872903807060280442896, 393248, 374144430356084407162070026681953532826823861731392] ![(.leaf 0 (Common.fact 866).pointIds 866), (.leaf 1 (Common.fact 888).pointIds 888), (.leaf 2 (Common.fact 889).pointIds 889), B1243, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 607).pointIds 607)]
theorem treeEq1242 : B1242.tree = HexagonCover.NBand.M8500_8700.SplitData.node1242 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1243
  · rfl
  · rfl
  · rfl

def B1241 : Block := .branch 168 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 680564734317245902012335240424800149512, 1329227995784915872903807060280442896, 5708990770823839524233143877797980545531379744, 11199373260101926709506585079794905130729536] ![(.leaf 0 (Common.fact 876).pointIds 876), (.leaf 1 (Common.fact 886).pointIds 886), (.leaf 2 (Common.fact 887).pointIds 887), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 574).pointIds 574), B1242]
theorem treeEq1241 : B1241.tree = HexagonCover.NBand.M8500_8700.SplitData.node1241 := by
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
  · exact treeEq1242

def B1240 : Block := .branch 152 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 680564734317245902012335240424800149512, 1393797904136159731261855295847582874566672, 393248, 11199415795397791826814518001620834101755968] ![(.leaf 0 (Common.fact 354).pointIds 354), (.leaf 1 (Common.fact 355).pointIds 355), (.leaf 2 (Common.fact 356).pointIds 356), (.leaf 3 (Common.fact 357).pointIds 357), (.leaf 4 (Common.fact 358).pointIds 358), B1241, (.leaf 6 (Common.fact 602).pointIds 602)]
theorem treeEq1240 : B1240.tree = HexagonCover.NBand.M8500_8700.SplitData.node1240 := by
  change Tree.branch (152 : Fin 175) _ = Tree.branch (152 : Fin 175) _
  apply congrArg (Tree.branch (152 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1241
  · rfl

def B1218 : Block := .branch 132 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 680564734317245902012335240424800149512, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B1219, (.leaf 5 (Common.fact 329).pointIds 329), B1240]
theorem treeEq1218 : B1218.tree = HexagonCover.NBand.M8500_8700.SplitData.node1218 := by
  change Tree.branch (132 : Fin 175) _ = Tree.branch (132 : Fin 175) _
  apply congrArg (Tree.branch (132 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1219
  · rfl
  · exact treeEq1240

def B1250 : Block := .branch 169 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 894).pointIds 894), (.leaf 2 (Common.fact 895).pointIds 895), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq1250 : B1250.tree = HexagonCover.NBand.M8500_8700.SplitData.node1250 := by
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

def B1249 : Block := .branch 170 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 892).pointIds 892), (.leaf 2 (Common.fact 893).pointIds 893), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1250, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq1249 : B1249.tree = HexagonCover.NBand.M8500_8700.SplitData.node1249 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1250
  · rfl

def B1248 : Block := .branch 163 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 684553066866338991398914202356418707472, 233840261972944466912589573234605283144949207269408, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 618).pointIds 618), (.leaf 5 (Common.fact 387).pointIds 387), B1249]
theorem treeEq1248 : B1248.tree = HexagonCover.NBand.M8500_8700.SplitData.node1248 := by
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
  · exact treeEq1249

def B1247 : Block := .branch 165 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 684553066866338991398914202356418707472, 187072209578355573530071658587684226515959365894176, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 617).pointIds 617), B1248, (.leaf 0 [] 0)]
theorem treeEq1247 : B1247.tree = HexagonCover.NBand.M8500_8700.SplitData.node1247 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1248
  · rfl

def B1246 : Block := .branch 167 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 684553066866338991398914202356418707472, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 616).pointIds 616), B1247, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq1246 : B1246.tree = HexagonCover.NBand.M8500_8700.SplitData.node1246 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1247
  · rfl

def B1217 : Block := .branch 129 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 475368975085586025561263726600, 1393800563241188408410454557028015476408336, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), (.leaf 2 (Common.fact 322).pointIds 322), B1218, B1246, (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 6 (Common.fact 324).pointIds 324)]
theorem treeEq1217 : B1217.tree = HexagonCover.NBand.M8500_8700.SplitData.node1217 := by
  change Tree.branch (129 : Fin 175) _ = Tree.branch (129 : Fin 175) _
  apply congrArg (Tree.branch (129 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1218
  · exact treeEq1246
  · rfl
  · rfl

theorem accepted1217 : B1217.accepted = true := by decide +kernel
theorem checked1217 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node1217 (maskNeeds ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 475368975085586025561263726600, 1393800563241188408410454557028015476408336, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq1217]
  exact B1217.sound accepted1217
#print axioms checked1217

def B1279 : Block := .branch 169 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 3367299783604329065772481548669487163363265418362944] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 894).pointIds 894), (.leaf 2 (Common.fact 895).pointIds 895), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 444).pointIds 444)]
theorem treeEq1279 : B1279.tree = HexagonCover.NBand.M8500_8700.SplitData.node1279 := by
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

def B1278 : Block := .branch 170 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 3367299783604329065772481548669487163363265418362944] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 892).pointIds 892), (.leaf 2 (Common.fact 893).pointIds 893), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1279, (.leaf 6 (Common.fact 440).pointIds 440)]
theorem treeEq1278 : B1278.tree = HexagonCover.NBand.M8500_8700.SplitData.node1278 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1279
  · rfl

def B1277 : Block := .branch 171 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 5986310706855827496689809430367476432546391608287240, 1329227995784915872903807060280442896, 393248, 374144430350639889291335011266539539107915570348096] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 890).pointIds 890), (.leaf 2 (Common.fact 891).pointIds 891), (.leaf 3 (Common.fact 578).pointIds 578), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B1278]
theorem treeEq1277 : B1277.tree = HexagonCover.NBand.M8500_8700.SplitData.node1277 := by
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
  · exact treeEq1278

def B1276 : Block := .branch 172 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 393248, 374144430350639889291335011266539539107915570348096] ![(.leaf 0 (Common.fact 866).pointIds 866), (.leaf 1 (Common.fact 888).pointIds 888), (.leaf 2 (Common.fact 889).pointIds 889), B1277, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 452).pointIds 452)]
theorem treeEq1276 : B1276.tree = HexagonCover.NBand.M8500_8700.SplitData.node1276 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1277
  · rfl
  · rfl
  · rfl

def B1275 : Block := .branch 168 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 22300745198530623141535718272648361506373664, 11193928742231191694091171086075996839346240] ![(.leaf 0 (Common.fact 876).pointIds 876), (.leaf 1 (Common.fact 886).pointIds 886), (.leaf 2 (Common.fact 887).pointIds 887), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 517).pointIds 517), B1276]
theorem treeEq1275 : B1275.tree = HexagonCover.NBand.M8500_8700.SplitData.node1275 := by
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
  · exact treeEq1276

def B1281 : Block := .branch 171 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 5986310706855827496689650974042447903871204520386568, 1329227995784915872903807060280442896, 393248, 33451160338284096688146337959329517314506816] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 890).pointIds 890), (.leaf 2 (Common.fact 891).pointIds 891), (.leaf 3 (Common.fact 578).pointIds 578), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 684).pointIds 684)]
theorem treeEq1281 : B1281.tree = HexagonCover.NBand.M8500_8700.SplitData.node1281 := by
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

def B1280 : Block := .branch 172 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 348449143727357899236552655360504824356872, 1329227995784915872903807060280442896, 393248, 33451160338284096688146337959329517314506816] ![(.leaf 0 (Common.fact 866).pointIds 866), (.leaf 1 (Common.fact 888).pointIds 888), (.leaf 2 (Common.fact 889).pointIds 889), B1281, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 683).pointIds 683)]
theorem treeEq1280 : B1280.tree = HexagonCover.NBand.M8500_8700.SplitData.node1280 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1281
  · rfl
  · rfl
  · rfl

def B1274 : Block := .branch 144 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 340).pointIds 340), (.leaf 1 (Common.fact 341).pointIds 341), (.leaf 2 (Common.fact 342).pointIds 342), (.leaf 3 (Common.fact 343).pointIds 343), (.leaf 4 (Common.fact 344).pointIds 344), B1275, B1280]
theorem treeEq1274 : B1274.tree = HexagonCover.NBand.M8500_8700.SplitData.node1274 := by
  change Tree.branch (144 : Fin 175) _ = Tree.branch (144 : Fin 175) _
  apply congrArg (Tree.branch (144 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1275
  · exact treeEq1280

def B1287 : Block := .branch 169 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 3367299789179515365405137334053416731525355794858048] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 894).pointIds 894), (.leaf 2 (Common.fact 895).pointIds 895), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 586).pointIds 586)]
theorem treeEq1287 : B1287.tree = HexagonCover.NBand.M8500_8700.SplitData.node1287 := by
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

def B1286 : Block := .branch 170 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 3367299789179515365405137334053416731525355794858048] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 892).pointIds 892), (.leaf 2 (Common.fact 893).pointIds 893), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1287, (.leaf 6 (Common.fact 583).pointIds 583)]
theorem treeEq1286 : B1286.tree = HexagonCover.NBand.M8500_8700.SplitData.node1286 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1287
  · rfl

def B1285 : Block := .branch 171 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 5986310706855827496689809430367476432546391608287240, 1329227995784915872903807060280442896, 393248, 374144435925826188923990796650469107270005946843200] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 890).pointIds 890), (.leaf 2 (Common.fact 891).pointIds 891), (.leaf 3 (Common.fact 578).pointIds 578), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B1286]
theorem treeEq1285 : B1285.tree = HexagonCover.NBand.M8500_8700.SplitData.node1285 := by
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
  · exact treeEq1286

def B1284 : Block := .branch 172 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 393248, 374144435925826188923990796650469107270005946843200] ![(.leaf 0 (Common.fact 866).pointIds 866), (.leaf 1 (Common.fact 888).pointIds 888), (.leaf 2 (Common.fact 889).pointIds 889), B1285, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 577).pointIds 577)]
theorem treeEq1284 : B1284.tree = HexagonCover.NBand.M8500_8700.SplitData.node1284 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1285
  · rfl
  · rfl
  · rfl

def B1283 : Block := .branch 168 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 5708990770823839524233143877797980545531379744, 16769115041863847479475100654238087215841344] ![(.leaf 0 (Common.fact 876).pointIds 876), (.leaf 1 (Common.fact 886).pointIds 886), (.leaf 2 (Common.fact 887).pointIds 887), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 574).pointIds 574), B1284]
theorem treeEq1283 : B1283.tree = HexagonCover.NBand.M8500_8700.SplitData.node1283 := by
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
  · exact treeEq1284

def B1282 : Block := .branch 152 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 16769157582352009455317861204594512516087872] ![(.leaf 0 (Common.fact 354).pointIds 354), (.leaf 1 (Common.fact 355).pointIds 355), (.leaf 2 (Common.fact 356).pointIds 356), (.leaf 3 (Common.fact 357).pointIds 357), (.leaf 4 (Common.fact 358).pointIds 358), B1283, (.leaf 6 (Common.fact 685).pointIds 685)]
theorem treeEq1282 : B1282.tree = HexagonCover.NBand.M8500_8700.SplitData.node1282 := by
  change Tree.branch (152 : Fin 175) _ = Tree.branch (152 : Fin 175) _
  apply congrArg (Tree.branch (152 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1283
  · rfl

def B1273 : Block := .branch 142 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), B1274, (.leaf 5 (Common.fact 339).pointIds 339), B1282]
theorem treeEq1273 : B1273.tree = HexagonCover.NBand.M8500_8700.SplitData.node1273 := by
  change Tree.branch (142 : Fin 175) _ = Tree.branch (142 : Fin 175) _
  apply congrArg (Tree.branch (142 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1274
  · rfl
  · exact treeEq1282

theorem accepted1273 : B1273.accepted = true := by decide +kernel
theorem checked1273 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node1273 (maskNeeds ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 11193971282719353669933931636432422139592768]) := by
  rw [← treeEq1273]
  exact B1273.sound accepted1273
#print axioms checked1273

end HexagonCover.NBand.M8500_8700.SplitTree.Run0016
