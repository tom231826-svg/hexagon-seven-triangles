import HexagonCover.NBand.M8500_8700.SplitData
import HexagonCover.NBand.M8500_8700.SplitTree.Run0016
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8500_8700.SplitTree.Run0017
open OwnerTree HexagonCover.NBand.M8500_8700

abbrev Block := Chunk (n := 175) (Certificate := Fin 1173) (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck

def Tip1270_1273 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node1273 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 11193971282719353669933931636432422139592768] HexagonCover.NBand.M8500_8700.SplitTree.Run0016.checked1273
def B1292 : Block := .branch 169 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618506064983148595661900589669599936576] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 894).pointIds 894), (.leaf 2 (Common.fact 895).pointIds 895), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 688).pointIds 688)]
theorem treeEq1292 : B1292.tree = HexagonCover.NBand.M8500_8700.SplitData.node1292 := by
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

def B1291 : Block := .branch 170 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618506064983148595661900589669599936576] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 892).pointIds 892), (.leaf 2 (Common.fact 893).pointIds 893), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1292, (.leaf 6 (Common.fact 686).pointIds 686)]
theorem treeEq1291 : B1291.tree = HexagonCover.NBand.M8500_8700.SplitData.node1291 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1292
  · rfl

def B1290 : Block := .branch 163 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 353894991474808894234635949102411261509648, 233840261972944466912589573234605283144949207269408, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 589).pointIds 589), (.leaf 5 (Common.fact 387).pointIds 387), B1291]
theorem treeEq1290 : B1290.tree = HexagonCover.NBand.M8500_8700.SplitData.node1290 := by
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
  · exact treeEq1291

def B1289 : Block := .branch 165 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 353894991474808894234635949102411261509648, 187072209578355573530071658587684226515959365894176, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 588).pointIds 588), B1290, (.leaf 0 [] 0)]
theorem treeEq1289 : B1289.tree = HexagonCover.NBand.M8500_8700.SplitData.node1289 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1290
  · rfl

def B1288 : Block := .branch 167 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 353894991474808894234635949102411261509648, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 587).pointIds 587), B1289, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq1288 : B1288.tree = HexagonCover.NBand.M8500_8700.SplitData.node1288 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1289
  · rfl

def B1272 : Block := .branch 138 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 475368975085586025561263726600, 1399242422655931853994122743132803207102480, 393248, 11226638389943763762426415598745871887892544] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), Tip1270_1273, B1288, (.leaf 5 (Common.fact 333).pointIds 333), (.leaf 6 (Common.fact 334).pointIds 334)]
theorem treeEq1272 : B1272.tree = HexagonCover.NBand.M8500_8700.SplitData.node1272 := by
  change Tree.branch (138 : Fin 175) _ = Tree.branch (138 : Fin 175) _
  apply congrArg (Tree.branch (138 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1288
  · rfl
  · rfl

def B1298 : Block := .branch 169 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 3367299783609773583643216564084901157082173709746240] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 894).pointIds 894), (.leaf 2 (Common.fact 895).pointIds 895), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 615).pointIds 615)]
theorem treeEq1298 : B1298.tree = HexagonCover.NBand.M8500_8700.SplitData.node1298 := by
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

def B1297 : Block := .branch 170 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 3367299783609773583643216564084901157082173709746240] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 892).pointIds 892), (.leaf 2 (Common.fact 893).pointIds 893), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1298, (.leaf 6 (Common.fact 612).pointIds 612)]
theorem treeEq1297 : B1297.tree = HexagonCover.NBand.M8500_8700.SplitData.node1297 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1298
  · rfl

def B1296 : Block := .branch 171 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 5986310706508058917696610320707907583751124496179208, 1329227995784915872903807060280442896, 393248, 374144430356084407162070026681953532826823861731392] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 890).pointIds 890), (.leaf 2 (Common.fact 891).pointIds 891), (.leaf 3 (Common.fact 608).pointIds 608), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B1297]
theorem treeEq1296 : B1296.tree = HexagonCover.NBand.M8500_8700.SplitData.node1296 := by
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
  · exact treeEq1297

def B1295 : Block := .branch 172 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 680564734317245902012335240424800149512, 1329227995784915872903807060280442896, 393248, 374144430356084407162070026681953532826823861731392] ![(.leaf 0 (Common.fact 866).pointIds 866), (.leaf 1 (Common.fact 888).pointIds 888), (.leaf 2 (Common.fact 889).pointIds 889), B1296, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 607).pointIds 607)]
theorem treeEq1295 : B1295.tree = HexagonCover.NBand.M8500_8700.SplitData.node1295 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1296
  · rfl
  · rfl
  · rfl

def B1294 : Block := .branch 168 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 680564734317245902012335240424800149512, 1329227995784915872903807060280442896, 5708990770823839524233143877797980545531379744, 11199373260101926709506585079794905130729536] ![(.leaf 0 (Common.fact 876).pointIds 876), (.leaf 1 (Common.fact 886).pointIds 886), (.leaf 2 (Common.fact 887).pointIds 887), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 574).pointIds 574), B1295]
theorem treeEq1294 : B1294.tree = HexagonCover.NBand.M8500_8700.SplitData.node1294 := by
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
  · exact treeEq1295

def B1293 : Block := .branch 152 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 680564734317245902012335240424800149512, 1393797904136159731261855295847582874566672, 393248, 11199415800590088685349345630151330430976064] ![(.leaf 0 (Common.fact 354).pointIds 354), (.leaf 1 (Common.fact 355).pointIds 355), (.leaf 2 (Common.fact 356).pointIds 356), (.leaf 3 (Common.fact 357).pointIds 357), (.leaf 4 (Common.fact 358).pointIds 358), B1294, (.leaf 6 (Common.fact 689).pointIds 689)]
theorem treeEq1293 : B1293.tree = HexagonCover.NBand.M8500_8700.SplitData.node1293 := by
  change Tree.branch (152 : Fin 175) _ = Tree.branch (152 : Fin 175) _
  apply congrArg (Tree.branch (152 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1294
  · rfl

def B1271 : Block := .branch 132 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 680564734317245902012335240424800149512, 1393797904785196838578708749413894915719184, 393248, 11226638389943763762426415598745871887892544] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B1272, (.leaf 5 (Common.fact 329).pointIds 329), B1293]
theorem treeEq1271 : B1271.tree = HexagonCover.NBand.M8500_8700.SplitData.node1271 := by
  change Tree.branch (132 : Fin 175) _ = Tree.branch (132 : Fin 175) _
  apply congrArg (Tree.branch (132 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1272
  · rfl
  · exact treeEq1293

def B1303 : Block := .branch 169 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618506064983148595661900589669599936576] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 894).pointIds 894), (.leaf 2 (Common.fact 895).pointIds 895), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 688).pointIds 688)]
theorem treeEq1303 : B1303.tree = HexagonCover.NBand.M8500_8700.SplitData.node1303 := by
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

def B1302 : Block := .branch 170 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618506064983148595661900589669599936576] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 892).pointIds 892), (.leaf 2 (Common.fact 893).pointIds 893), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1303, (.leaf 6 (Common.fact 686).pointIds 686)]
theorem treeEq1302 : B1302.tree = HexagonCover.NBand.M8500_8700.SplitData.node1302 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1303
  · rfl

def B1301 : Block := .branch 163 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 684553066866338991398914202356418707472, 233840261972944466912589573234605283144949207269408, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 618).pointIds 618), (.leaf 5 (Common.fact 387).pointIds 387), B1302]
theorem treeEq1301 : B1301.tree = HexagonCover.NBand.M8500_8700.SplitData.node1301 := by
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
  · exact treeEq1302

def B1300 : Block := .branch 165 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 684553066866338991398914202356418707472, 187072209578355573530071658587684226515959365894176, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 617).pointIds 617), B1301, (.leaf 0 [] 0)]
theorem treeEq1300 : B1300.tree = HexagonCover.NBand.M8500_8700.SplitData.node1300 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1301
  · rfl

def B1299 : Block := .branch 167 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 684553066866338991398914202356418707472, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 616).pointIds 616), B1300, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq1299 : B1299.tree = HexagonCover.NBand.M8500_8700.SplitData.node1299 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1300
  · rfl

def B1270 : Block := .branch 129 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 475368975085586025561263726600, 1393800563241188408410454557028015476408336, 393248, 11226638389943763762426415598745871887892544] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), (.leaf 2 (Common.fact 322).pointIds 322), B1271, B1299, (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 6 (Common.fact 324).pointIds 324)]
theorem treeEq1270 : B1270.tree = HexagonCover.NBand.M8500_8700.SplitData.node1270 := by
  change Tree.branch (129 : Fin 175) _ = Tree.branch (129 : Fin 175) _
  apply congrArg (Tree.branch (129 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1271
  · exact treeEq1299
  · rfl
  · rfl

theorem accepted1270 : B1270.accepted = true := by decide +kernel
theorem checked1270 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node1270 (maskNeeds ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 475368975085586025561263726600, 1393800563241188408410454557028015476408336, 393248, 11226638389943763762426415598745871887892544]) := by
  rw [← treeEq1270]
  exact B1270.sound accepted1270
#print axioms checked1270

def Tip1213_1217 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node1217 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 475368975085586025561263726600, 1393800563241188408410454557028015476408336, 393248, 11226638384751466903891587970215375558672448] HexagonCover.NBand.M8500_8700.SplitTree.Run0016.checked1217
def B1254 : Block := .branch 171 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 5986310706507379017576607879913888757764604012027912, 1329227995784915872903807060280442896, 393248, 748288849507353694807469898273653799753954862039104] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 890).pointIds 890), (.leaf 2 (Common.fact 891).pointIds 891), (.leaf 3 (Common.fact 636).pointIds 636), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 692).pointIds 692)]
theorem treeEq1254 : B1254.tree = HexagonCover.NBand.M8500_8700.SplitData.node1254 := by
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

def B1253 : Block := .branch 172 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 664614314805107993509253904315998216, 1329227995784915872903807060280442896, 393248, 748288849507353694807469898273653799753954862039104] ![(.leaf 0 (Common.fact 866).pointIds 866), (.leaf 1 (Common.fact 888).pointIds 888), (.leaf 2 (Common.fact 889).pointIds 889), B1254, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 691).pointIds 691)]
theorem treeEq1253 : B1253.tree = HexagonCover.NBand.M8500_8700.SplitData.node1253 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1254
  · rfl
  · rfl
  · rfl

def B1252 : Block := .branch 169 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 664614473261433022037929091403898888, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 11193931400687183263922916893690117400035392] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 894).pointIds 894), (.leaf 2 (Common.fact 895).pointIds 895), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), B1253]
theorem treeEq1252 : B1252.tree = HexagonCover.NBand.M8500_8700.SplitData.node1252 := by
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
  · exact treeEq1253

def B1251 : Block := .branch 170 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 664614473261433022037929091403898888, 1329227995784915872903807060280442896, 393248, 11193973935983048381230849815516046371061824] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 892).pointIds 892), (.leaf 2 (Common.fact 893).pointIds 893), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1252, (.leaf 6 (Common.fact 643).pointIds 643)]
theorem treeEq1251 : B1251.tree = HexagonCover.NBand.M8500_8700.SplitData.node1251 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1252
  · rfl

def B1216 : Block := .branch 121 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 664614473261433022037929091403898888, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 315).pointIds 315), (.leaf 1 (Common.fact 316).pointIds 316), (.leaf 2 (Common.fact 317).pointIds 317), (.leaf 3 (Common.fact 318).pointIds 318), Tip1213_1217, (.leaf 5 (Common.fact 319).pointIds 319), B1251]
theorem treeEq1216 : B1216.tree = HexagonCover.NBand.M8500_8700.SplitData.node1216 := by
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
  · exact treeEq1251

def B1259 : Block := .branch 169 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 894).pointIds 894), (.leaf 2 (Common.fact 895).pointIds 895), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq1259 : B1259.tree = HexagonCover.NBand.M8500_8700.SplitData.node1259 := by
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

def B1258 : Block := .branch 170 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 892).pointIds 892), (.leaf 2 (Common.fact 893).pointIds 893), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1259, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq1258 : B1258.tree = HexagonCover.NBand.M8500_8700.SplitData.node1258 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1259
  · rfl

def B1257 : Block := .branch 163 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1994491030784690662809276902461767696, 233840261972944466912589573234605283144949207269408, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 387).pointIds 387), B1258]
theorem treeEq1257 : B1257.tree = HexagonCover.NBand.M8500_8700.SplitData.node1257 := by
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
  · exact treeEq1258

def B1256 : Block := .branch 165 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1994491030784690662809276902461767696, 187072209578355573530071658587684226515959365894176, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 645).pointIds 645), B1257, (.leaf 0 [] 0)]
theorem treeEq1256 : B1256.tree = HexagonCover.NBand.M8500_8700.SplitData.node1256 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1257
  · rfl

def B1255 : Block := .branch 167 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1994491030784690662809276902461767696, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 644).pointIds 644), B1256, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq1255 : B1255.tree = HexagonCover.NBand.M8500_8700.SplitData.node1255 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1256
  · rfl

def B1215 : Block := .branch 119 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 475368975085586025561263726600, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 310).pointIds 310), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), B1216, B1255, (.leaf 5 (Common.fact 313).pointIds 313), (.leaf 6 (Common.fact 314).pointIds 314)]
theorem treeEq1215 : B1215.tree = HexagonCover.NBand.M8500_8700.SplitData.node1215 := by
  change Tree.branch (119 : Fin 175) _ = Tree.branch (119 : Fin 175) _
  apply congrArg (Tree.branch (119 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1216
  · exact treeEq1255
  · rfl
  · rfl

def B1261 : Block := .branch 171 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 5986310706507378353287128541114379032644229892431880, 1329227995784915872903807060280442896, 393248, 11193971298296244245538414522023911127253056] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 890).pointIds 890), (.leaf 2 (Common.fact 891).pointIds 891), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq1261 : B1261.tree = HexagonCover.NBand.M8500_8700.SplitData.node1261 := by
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

def B1260 : Block := .branch 172 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 324835466308483784133530196402184, 1329227995784915872903807060280442896, 393248, 11193971298296244245538414522023911127253056] ![(.leaf 0 (Common.fact 866).pointIds 866), (.leaf 1 (Common.fact 888).pointIds 888), (.leaf 2 (Common.fact 889).pointIds 889), B1261, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 666).pointIds 666)]
theorem treeEq1260 : B1260.tree = HexagonCover.NBand.M8500_8700.SplitData.node1260 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1261
  · rfl
  · rfl
  · rfl

def B1214 : Block := .branch 114 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 324993922633512312808717284302856, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448] ![B1215, (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 308).pointIds 308), (.leaf 5 (Common.fact 309).pointIds 309), B1260]
theorem treeEq1214 : B1214.tree = HexagonCover.NBand.M8500_8700.SplitData.node1214 := by
  change Tree.branch (114 : Fin 175) _ = Tree.branch (114 : Fin 175) _
  apply congrArg (Tree.branch (114 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq1215
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1260

def B1265 : Block := .branch 169 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 894).pointIds 894), (.leaf 2 (Common.fact 895).pointIds 895), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq1265 : B1265.tree = HexagonCover.NBand.M8500_8700.SplitData.node1265 := by
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

def B1264 : Block := .branch 170 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 892).pointIds 892), (.leaf 2 (Common.fact 893).pointIds 893), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1265, (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq1264 : B1264.tree = HexagonCover.NBand.M8500_8700.SplitData.node1264 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1265
  · rfl

def B1263 : Block := .branch 171 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 5986310706507378353287286997439407561319416980332552, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 890).pointIds 890), (.leaf 2 (Common.fact 891).pointIds 891), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B1264]
theorem treeEq1263 : B1263.tree = HexagonCover.NBand.M8500_8700.SplitData.node1263 := by
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
  · exact treeEq1264

def B1262 : Block := .branch 172 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 866).pointIds 866), (.leaf 1 (Common.fact 888).pointIds 888), (.leaf 2 (Common.fact 889).pointIds 889), B1263, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq1262 : B1262.tree = HexagonCover.NBand.M8500_8700.SplitData.node1262 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1263
  · rfl
  · rfl
  · rfl

def B1213 : Block := .branch 113 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 324993922633512312808717284302856, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448] ![B1214, (.leaf 1 (Common.fact 300).pointIds 300), (.leaf 2 (Common.fact 301).pointIds 301), (.leaf 3 (Common.fact 302).pointIds 302), (.leaf 4 (Common.fact 303).pointIds 303), (.leaf 5 (Common.fact 304).pointIds 304), B1262]
theorem treeEq1213 : B1213.tree = HexagonCover.NBand.M8500_8700.SplitData.node1213 := by
  change Tree.branch (113 : Fin 175) _ = Tree.branch (113 : Fin 175) _
  apply congrArg (Tree.branch (113 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq1214
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1262

theorem accepted1213 : B1213.accepted = true := by decide +kernel
theorem checked1213 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node1213 (maskNeeds ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 324993922633512312808717284302856, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq1213]
  exact B1213.sound accepted1213
#print axioms checked1213

def Tip1212_1270 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node1270 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 475368975085586025561263726600, 1393800563241188408410454557028015476408336, 393248, 11226638389943763762426415598745871887892544] checked1270
def Tip1212_1213 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node1213 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 324993922633512312808717284302856, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448] checked1213
def B1307 : Block := .branch 171 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 5986310706507379017576607879913888757764604012027912, 1329227995784915872903807060280442896, 393248, 748288849507353694807469898273653799753954862039104] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 890).pointIds 890), (.leaf 2 (Common.fact 891).pointIds 891), (.leaf 3 (Common.fact 636).pointIds 636), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 692).pointIds 692)]
theorem treeEq1307 : B1307.tree = HexagonCover.NBand.M8500_8700.SplitData.node1307 := by
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

def B1306 : Block := .branch 172 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 664614314805107993509253904315998216, 1329227995784915872903807060280442896, 393248, 748288849507353694807469898273653799753954862039104] ![(.leaf 0 (Common.fact 866).pointIds 866), (.leaf 1 (Common.fact 888).pointIds 888), (.leaf 2 (Common.fact 889).pointIds 889), B1307, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 691).pointIds 691)]
theorem treeEq1306 : B1306.tree = HexagonCover.NBand.M8500_8700.SplitData.node1306 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1307
  · rfl
  · rfl
  · rfl

def B1305 : Block := .branch 169 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 664614473261433022037929091403898888, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 11193931400687183263922916893690117400035392] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 894).pointIds 894), (.leaf 2 (Common.fact 895).pointIds 895), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), B1306]
theorem treeEq1305 : B1305.tree = HexagonCover.NBand.M8500_8700.SplitData.node1305 := by
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
  · exact treeEq1306

def B1304 : Block := .branch 170 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 664614473261433022037929091403898888, 1329227995784915872903807060280442896, 393248, 11193973941175345239765677444046542700281920] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 892).pointIds 892), (.leaf 2 (Common.fact 893).pointIds 893), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1305, (.leaf 6 (Common.fact 690).pointIds 690)]
theorem treeEq1304 : B1304.tree = HexagonCover.NBand.M8500_8700.SplitData.node1304 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1305
  · rfl

def B1269 : Block := .branch 121 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 664614473261433022037929091403898888, 1393797904785196838578708749413894915719184, 393248, 11226638389943763762426415598745871887892544] ![(.leaf 0 (Common.fact 315).pointIds 315), (.leaf 1 (Common.fact 316).pointIds 316), (.leaf 2 (Common.fact 317).pointIds 317), (.leaf 3 (Common.fact 318).pointIds 318), Tip1212_1270, (.leaf 5 (Common.fact 319).pointIds 319), B1304]
theorem treeEq1269 : B1269.tree = HexagonCover.NBand.M8500_8700.SplitData.node1269 := by
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
  · exact treeEq1304

def B1312 : Block := .branch 169 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618506064983148595661900589669599936576] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 894).pointIds 894), (.leaf 2 (Common.fact 895).pointIds 895), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 688).pointIds 688)]
theorem treeEq1312 : B1312.tree = HexagonCover.NBand.M8500_8700.SplitData.node1312 := by
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

def B1311 : Block := .branch 170 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618506064983148595661900589669599936576] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 892).pointIds 892), (.leaf 2 (Common.fact 893).pointIds 893), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1312, (.leaf 6 (Common.fact 686).pointIds 686)]
theorem treeEq1311 : B1311.tree = HexagonCover.NBand.M8500_8700.SplitData.node1311 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1312
  · rfl

def B1310 : Block := .branch 163 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1994491030784690662809276902461767696, 233840261972944466912589573234605283144949207269408, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 387).pointIds 387), B1311]
theorem treeEq1310 : B1310.tree = HexagonCover.NBand.M8500_8700.SplitData.node1310 := by
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
  · exact treeEq1311

def B1309 : Block := .branch 165 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1994491030784690662809276902461767696, 187072209578355573530071658587684226515959365894176, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 645).pointIds 645), B1310, (.leaf 0 [] 0)]
theorem treeEq1309 : B1309.tree = HexagonCover.NBand.M8500_8700.SplitData.node1309 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1310
  · rfl

def B1308 : Block := .branch 167 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1994491030784690662809276902461767696, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 644).pointIds 644), B1309, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq1308 : B1308.tree = HexagonCover.NBand.M8500_8700.SplitData.node1308 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1309
  · rfl

def B1268 : Block := .branch 119 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 475368975085586025561263726600, 1393797904785196838578708749413894915719184, 393248, 11226638389943763762426415598745871887892544] ![(.leaf 0 (Common.fact 310).pointIds 310), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), B1269, B1308, (.leaf 5 (Common.fact 313).pointIds 313), (.leaf 6 (Common.fact 314).pointIds 314)]
theorem treeEq1268 : B1268.tree = HexagonCover.NBand.M8500_8700.SplitData.node1268 := by
  change Tree.branch (119 : Fin 175) _ = Tree.branch (119 : Fin 175) _
  apply congrArg (Tree.branch (119 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1269
  · exact treeEq1308
  · rfl
  · rfl

def B1314 : Block := .branch 171 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 5986310706507378353287128541114379032644229892431880, 1329227995784915872903807060280442896, 393248, 11193971298296244245538414522023911127253056] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 890).pointIds 890), (.leaf 2 (Common.fact 891).pointIds 891), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq1314 : B1314.tree = HexagonCover.NBand.M8500_8700.SplitData.node1314 := by
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

def B1313 : Block := .branch 172 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 324835466308483784133530196402184, 1329227995784915872903807060280442896, 393248, 11193971298296244245538414522023911127253056] ![(.leaf 0 (Common.fact 866).pointIds 866), (.leaf 1 (Common.fact 888).pointIds 888), (.leaf 2 (Common.fact 889).pointIds 889), B1314, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 666).pointIds 666)]
theorem treeEq1313 : B1313.tree = HexagonCover.NBand.M8500_8700.SplitData.node1313 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1314
  · rfl
  · rfl
  · rfl

def B1267 : Block := .branch 114 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 324993922633512312808717284302856, 1393797904785196838578708749413894915719184, 393248, 11226638389943763762426415598745871887892544] ![B1268, (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 308).pointIds 308), (.leaf 5 (Common.fact 309).pointIds 309), B1313]
theorem treeEq1267 : B1267.tree = HexagonCover.NBand.M8500_8700.SplitData.node1267 := by
  change Tree.branch (114 : Fin 175) _ = Tree.branch (114 : Fin 175) _
  apply congrArg (Tree.branch (114 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq1268
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1313

def B1318 : Block := .branch 169 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 894).pointIds 894), (.leaf 2 (Common.fact 895).pointIds 895), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq1318 : B1318.tree = HexagonCover.NBand.M8500_8700.SplitData.node1318 := by
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

def B1317 : Block := .branch 170 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 892).pointIds 892), (.leaf 2 (Common.fact 893).pointIds 893), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1318, (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq1317 : B1317.tree = HexagonCover.NBand.M8500_8700.SplitData.node1317 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1318
  · rfl

def B1316 : Block := .branch 171 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 5986310706507378353287286997439407561319416980332552, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 890).pointIds 890), (.leaf 2 (Common.fact 891).pointIds 891), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B1317]
theorem treeEq1316 : B1316.tree = HexagonCover.NBand.M8500_8700.SplitData.node1316 := by
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
  · exact treeEq1317

def B1315 : Block := .branch 172 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 866).pointIds 866), (.leaf 1 (Common.fact 888).pointIds 888), (.leaf 2 (Common.fact 889).pointIds 889), B1316, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq1315 : B1315.tree = HexagonCover.NBand.M8500_8700.SplitData.node1315 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1316
  · rfl
  · rfl
  · rfl

def B1266 : Block := .branch 113 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 324993922633512312808717284302856, 1393797904785196838578708749413894915719184, 393248, 11226638389943763762426415598745871887892544] ![B1267, (.leaf 1 (Common.fact 300).pointIds 300), (.leaf 2 (Common.fact 301).pointIds 301), (.leaf 3 (Common.fact 302).pointIds 302), (.leaf 4 (Common.fact 303).pointIds 303), (.leaf 5 (Common.fact 304).pointIds 304), B1315]
theorem treeEq1266 : B1266.tree = HexagonCover.NBand.M8500_8700.SplitData.node1266 := by
  change Tree.branch (113 : Fin 175) _ = Tree.branch (113 : Fin 175) _
  apply congrArg (Tree.branch (113 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq1267
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1315

def B1212 : Block := .branch 112 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 324993922633512312808717284302856, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448] ![Tip1212_1213, (.leaf 1 (Common.fact 295).pointIds 295), (.leaf 2 (Common.fact 296).pointIds 296), (.leaf 3 (Common.fact 297).pointIds 297), (.leaf 4 (Common.fact 298).pointIds 298), (.leaf 5 (Common.fact 299).pointIds 299), B1266]
theorem treeEq1212 : B1212.tree = HexagonCover.NBand.M8500_8700.SplitData.node1212 := by
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
  · exact treeEq1266

theorem accepted1212 : B1212.accepted = true := by decide +kernel
theorem checked1212 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node1212 (maskNeeds ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 324993922633512312808717284302856, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq1212]
  exact B1212.sound accepted1212
#print axioms checked1212

def Tip1208_1212 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node1212 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 324993922633512312808717284302856, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448] checked1212
def B1320 : Block := .branch 168 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 11193971278176093918715957461468237851525184] ![(.leaf 0 (Common.fact 876).pointIds 876), (.leaf 1 (Common.fact 886).pointIds 886), (.leaf 2 (Common.fact 887).pointIds 887), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 765).pointIds 765), (.leaf 6 (Common.fact 706).pointIds 706)]
theorem treeEq1320 : B1320.tree = HexagonCover.NBand.M8500_8700.SplitData.node1320 := by
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

def B1319 : Block := .branch 170 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 11193971278176093918715957461468237851525184] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 892).pointIds 892), (.leaf 2 (Common.fact 893).pointIds 893), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1320, (.leaf 6 (Common.fact 760).pointIds 760)]
theorem treeEq1319 : B1319.tree = HexagonCover.NBand.M8500_8700.SplitData.node1319 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1320
  · rfl

def B1211 : Block := .branch 109 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 325073150796026577146310828253192, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 290).pointIds 290), (.leaf 1 (Common.fact 291).pointIds 291), (.leaf 2 (Common.fact 292).pointIds 292), (.leaf 3 (Common.fact 293).pointIds 293), Tip1208_1212, (.leaf 5 (Common.fact 294).pointIds 294), B1319]
theorem treeEq1211 : B1211.tree = HexagonCover.NBand.M8500_8700.SplitData.node1211 := by
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
  · exact treeEq1319

def B1325 : Block := .branch 169 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 894).pointIds 894), (.leaf 2 (Common.fact 895).pointIds 895), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq1325 : B1325.tree = HexagonCover.NBand.M8500_8700.SplitData.node1325 := by
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

def B1324 : Block := .branch 170 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 892).pointIds 892), (.leaf 2 (Common.fact 893).pointIds 893), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1325, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq1324 : B1324.tree = HexagonCover.NBand.M8500_8700.SplitData.node1324 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1325
  · rfl

def B1323 : Block := .branch 163 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329552514338574299630590216301019152, 233840261972944466912589573234605283144949207269408, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 709).pointIds 709), (.leaf 5 (Common.fact 387).pointIds 387), B1324]
theorem treeEq1323 : B1323.tree = HexagonCover.NBand.M8500_8700.SplitData.node1323 := by
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
  · exact treeEq1324

def B1322 : Block := .branch 165 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329552514338574299630590216301019152, 187072209578355573530071658587684226515959365894176, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 708).pointIds 708), B1323, (.leaf 0 [] 0)]
theorem treeEq1322 : B1322.tree = HexagonCover.NBand.M8500_8700.SplitData.node1322 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1323
  · rfl

def B1321 : Block := .branch 167 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329552514338574299630590216301019152, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 707).pointIds 707), B1322, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq1321 : B1321.tree = HexagonCover.NBand.M8500_8700.SplitData.node1321 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1322
  · rfl

def B1210 : Block := .branch 108 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 554597137599850363154807676936, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), B1211, B1321, (.leaf 5 (Common.fact 288).pointIds 288), (.leaf 6 (Common.fact 289).pointIds 289)]
theorem treeEq1210 : B1210.tree = HexagonCover.NBand.M8500_8700.SplitData.node1210 := by
  change Tree.branch (108 : Fin 175) _ = Tree.branch (108 : Fin 175) _
  apply congrArg (Tree.branch (108 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1211
  · exact treeEq1321
  · rfl
  · rfl

def B1327 : Block := .branch 171 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 5986310706507378352962609987455952305861073871855624, 1329227995784915872903807060280442896, 393248, 11193971277528324461999332237303422513578048] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 890).pointIds 890), (.leaf 2 (Common.fact 891).pointIds 891), (.leaf 3 (Common.fact 766).pointIds 766), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 726).pointIds 726)]
theorem treeEq1327 : B1327.tree = HexagonCover.NBand.M8500_8700.SplitData.node1327 := by
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

def B1326 : Block := .branch 172 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 316912650057057350374175825928, 1329227995784915872903807060280442896, 393248, 11193971277528324461999332237303422513578048] ![(.leaf 0 (Common.fact 866).pointIds 866), (.leaf 1 (Common.fact 888).pointIds 888), (.leaf 2 (Common.fact 889).pointIds 889), B1327, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 728).pointIds 728)]
theorem treeEq1326 : B1326.tree = HexagonCover.NBand.M8500_8700.SplitData.node1326 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1327
  · rfl
  · rfl
  · rfl

def B1209 : Block := .branch 100 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 554597137599850363154807676936, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448] ![B1210, (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 281).pointIds 281), (.leaf 3 (Common.fact 282).pointIds 282), (.leaf 4 (Common.fact 283).pointIds 283), (.leaf 5 (Common.fact 284).pointIds 284), B1326]
theorem treeEq1209 : B1209.tree = HexagonCover.NBand.M8500_8700.SplitData.node1209 := by
  change Tree.branch (100 : Fin 175) _ = Tree.branch (100 : Fin 175) _
  apply congrArg (Tree.branch (100 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq1210
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1326

def B1332 : Block := .branch 169 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 894).pointIds 894), (.leaf 2 (Common.fact 895).pointIds 895), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq1332 : B1332.tree = HexagonCover.NBand.M8500_8700.SplitData.node1332 := by
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

def B1331 : Block := .branch 170 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 892).pointIds 892), (.leaf 2 (Common.fact 893).pointIds 893), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1332, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq1331 : B1331.tree = HexagonCover.NBand.M8500_8700.SplitData.node1331 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1332
  · rfl

def B1330 : Block := .branch 163 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329228312697565929961157434456244240, 233840261972944466912589573234605283144949207269408, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 731).pointIds 731), (.leaf 5 (Common.fact 387).pointIds 387), B1331]
theorem treeEq1330 : B1330.tree = HexagonCover.NBand.M8500_8700.SplitData.node1330 := by
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
  · exact treeEq1331

def B1329 : Block := .branch 165 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329228312697565929961157434456244240, 187072209578355573530071658587684226515959365894176, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 730).pointIds 730), B1330, (.leaf 0 [] 0)]
theorem treeEq1329 : B1329.tree = HexagonCover.NBand.M8500_8700.SplitData.node1329 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1330
  · rfl

def B1328 : Block := .branch 167 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329228312697565929961157434456244240, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 729).pointIds 729), B1329, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq1328 : B1328.tree = HexagonCover.NBand.M8500_8700.SplitData.node1328 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1329
  · rfl

def B1208 : Block := .branch 98 ![1237940335011998006369059201, 151152620940525821756930, 75576310469988032976900, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 275).pointIds 275), (.leaf 1 (Common.fact 276).pointIds 276), (.leaf 2 (Common.fact 277).pointIds 277), B1209, B1328, (.leaf 5 (Common.fact 278).pointIds 278), (.leaf 6 (Common.fact 279).pointIds 279)]
theorem treeEq1208 : B1208.tree = HexagonCover.NBand.M8500_8700.SplitData.node1208 := by
  change Tree.branch (98 : Fin 175) _ = Tree.branch (98 : Fin 175) _
  apply congrArg (Tree.branch (98 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1209
  · exact treeEq1328
  · rfl
  · rfl

theorem accepted1208 : B1208.accepted = true := by decide +kernel
theorem checked1208 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node1208 (maskNeeds ![1237940335011998006369059201, 151152620940525821756930, 75576310469988032976900, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq1208]
  exact B1208.sound accepted1208
#print axioms checked1208

end HexagonCover.NBand.M8500_8700.SplitTree.Run0017
