import HexagonCover.NBand.M7100_7300.SplitData
import HexagonCover.NBand.M7100_7300.SplitTree.Run0003
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7100_7300.SplitTree.Run0004
open OwnerTree HexagonCover.NBand.M7100_7300

abbrev Block := Chunk (n := 173) (Certificate := Fin 933) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip0077_0078 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0078 ![385, 360289069701268994, 55376261018147624964, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257283796722853571625821405248] HexagonCover.NBand.M7100_7300.SplitTree.Run0003.checked0078
def B0366 : Block := .branch 79 ![374144419156732414708075875829334913944883216515457, 730750818665451459101842416358141510927477900802, 6148, 24584, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 758).pointIds 758), (.leaf 1 (Common.fact 717).pointIds 717), (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), (.leaf 5 (Common.fact 224).pointIds 224), (.leaf 6 (Common.fact 805).pointIds 805)]
theorem treeEq0366 : B0366.tree = HexagonCover.NBand.M7100_7300.SplitData.node0366 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0365 : Block := .branch 159 ![374144419156732414708075875829334913944883216515457, 1099511629314, 6148, 24584, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 760).pointIds 760), B0366, (.leaf 2 (Common.fact 228).pointIds 228), (.leaf 3 (Common.fact 229).pointIds 229), (.leaf 4 (Common.fact 230).pointIds 230), (.leaf 5 (Common.fact 231).pointIds 231), (.leaf 6 (Common.fact 804).pointIds 804)]
theorem treeEq0365 : B0365.tree = HexagonCover.NBand.M7100_7300.SplitData.node0365 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0366
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0364 : Block := .branch 124 ![374144419156711147060143317175368453031918731002241, 1099511629314, 6148, 24584, 98320, 393248, 21778071483256974311749925714704515727424] ![B0365, (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), (.leaf 4 (Common.fact 191).pointIds 191), (.leaf 5 (Common.fact 192).pointIds 192), (.leaf 6 (Common.fact 803).pointIds 803)]
theorem treeEq0364 : B0364.tree = HexagonCover.NBand.M7100_7300.SplitData.node0364 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0365
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0363 : Block := .branch 135 ![374144419156711147060143317175368453031918731002241, 1099511629314, 6148, 24584, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), (.leaf 4 (Common.fact 419).pointIds 419), B0364, (.leaf 6 (Common.fact 802).pointIds 802)]
theorem treeEq0363 : B0363.tree = HexagonCover.NBand.M7100_7300.SplitData.node0363 := by
  change Tree.branch (135 : Fin 173) _ = Tree.branch (135 : Fin 173) _
  apply congrArg (Tree.branch (135 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0364
  · rfl

def B0362 : Block := .branch 138 ![374144419156711147060143317175368453031918731002241, 1099511629314, 6148, 38685626227668133590622216, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 116).pointIds 116), (.leaf 1 (Common.fact 117).pointIds 117), (.leaf 2 (Common.fact 118).pointIds 118), (.leaf 3 (Common.fact 119).pointIds 119), B0363, (.leaf 5 (Common.fact 120).pointIds 120), (.leaf 6 (Common.fact 801).pointIds 801)]
theorem treeEq0362 : B0362.tree = HexagonCover.NBand.M7100_7300.SplitData.node0362 := by
  change Tree.branch (138 : Fin 173) _ = Tree.branch (138 : Fin 173) _
  apply congrArg (Tree.branch (138 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0363
  · rfl
  · rfl

def B0361 : Block := .branch 139 ![374144419156711147060143317175368453031918731002241, 1099511629314, 6148, 38685626227668133590622216, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 110).pointIds 110), (.leaf 1 (Common.fact 111).pointIds 111), (.leaf 2 (Common.fact 112).pointIds 112), (.leaf 3 (Common.fact 113).pointIds 113), B0362, (.leaf 5 (Common.fact 114).pointIds 114), (.leaf 6 (Common.fact 800).pointIds 800)]
theorem treeEq0361 : B0361.tree = HexagonCover.NBand.M7100_7300.SplitData.node0361 := by
  change Tree.branch (139 : Fin 173) _ = Tree.branch (139 : Fin 173) _
  apply congrArg (Tree.branch (139 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0362
  · rfl
  · rfl

def B0360 : Block := .branch 140 ![374144419156711147060143317175368453031918731002241, 1099511629314, 6148, 38685626227668133590622216, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 104).pointIds 104), (.leaf 1 (Common.fact 105).pointIds 105), (.leaf 2 (Common.fact 106).pointIds 106), (.leaf 3 (Common.fact 107).pointIds 107), B0361, (.leaf 5 (Common.fact 108).pointIds 108), (.leaf 6 (Common.fact 799).pointIds 799)]
theorem treeEq0360 : B0360.tree = HexagonCover.NBand.M7100_7300.SplitData.node0360 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0361
  · rfl
  · rfl

def B0359 : Block := .branch 141 ![374144419156711147060143317175368453031918731002241, 1099511629314, 6148, 38685626227668133590622216, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 98).pointIds 98), (.leaf 1 (Common.fact 99).pointIds 99), (.leaf 2 (Common.fact 100).pointIds 100), (.leaf 3 (Common.fact 101).pointIds 101), B0360, (.leaf 5 (Common.fact 102).pointIds 102), (.leaf 6 (Common.fact 798).pointIds 798)]
theorem treeEq0359 : B0359.tree = HexagonCover.NBand.M7100_7300.SplitData.node0359 := by
  change Tree.branch (141 : Fin 173) _ = Tree.branch (141 : Fin 173) _
  apply congrArg (Tree.branch (141 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0360
  · rfl
  · rfl

def B0358 : Block := .branch 129 ![374144419156711147060143317175368453031918731002241, 1099511629314, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 298).pointIds 298), (.leaf 2 (Common.fact 299).pointIds 299), (.leaf 3 (Common.fact 300).pointIds 300), (.leaf 4 (Common.fact 565).pointIds 565), (.leaf 5 (Common.fact 301).pointIds 301), B0359]
theorem treeEq0358 : B0358.tree = HexagonCover.NBand.M7100_7300.SplitData.node0358 := by
  change Tree.branch (129 : Fin 173) _ = Tree.branch (129 : Fin 173) _
  apply congrArg (Tree.branch (129 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0359

def B0357 : Block := .branch 130 ![374144419156711147060143317175368453031918731002241, 1099511629314, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 559).pointIds 559), (.leaf 1 (Common.fact 560).pointIds 560), (.leaf 2 (Common.fact 561).pointIds 561), (.leaf 3 (Common.fact 562).pointIds 562), (.leaf 4 (Common.fact 563).pointIds 563), (.leaf 5 (Common.fact 564).pointIds 564), B0358]
theorem treeEq0357 : B0357.tree = HexagonCover.NBand.M7100_7300.SplitData.node0357 := by
  change Tree.branch (130 : Fin 173) _ = Tree.branch (130 : Fin 173) _
  apply congrArg (Tree.branch (130 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0358

def B0356 : Block := .branch 131 ![374144419156711147060143317175368453031918731002241, 1099511629314, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 548).pointIds 548), (.leaf 1 (Common.fact 549).pointIds 549), (.leaf 2 (Common.fact 550).pointIds 550), (.leaf 3 (Common.fact 551).pointIds 551), (.leaf 4 (Common.fact 552).pointIds 552), (.leaf 5 (Common.fact 553).pointIds 553), B0357]
theorem treeEq0356 : B0356.tree = HexagonCover.NBand.M7100_7300.SplitData.node0356 := by
  change Tree.branch (131 : Fin 173) _ = Tree.branch (131 : Fin 173) _
  apply congrArg (Tree.branch (131 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0357

def B0355 : Block := .branch 163 ![374144419156711147060143317175368453031918731002241, 1099511629314, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 539).pointIds 539), (.leaf 5 (Common.fact 248).pointIds 248), B0356]
theorem treeEq0355 : B0355.tree = HexagonCover.NBand.M7100_7300.SplitData.node0355 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0356

def B0354 : Block := .branch 165 ![374144419156711147060143317175368453031918731002241, 1099511629314, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 538).pointIds 538), B0355, (.leaf 0 [] 0)]
theorem treeEq0354 : B0354.tree = HexagonCover.NBand.M7100_7300.SplitData.node0354 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0355
  · rfl

def B0353 : Block := .branch 167 ![374144419156711147060143317175368453031918731002241, 1099511629314, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 532).pointIds 532), (.leaf 1 (Common.fact 533).pointIds 533), (.leaf 2 (Common.fact 534).pointIds 534), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 536).pointIds 536), B0354, (.leaf 6 (Common.fact 537).pointIds 537)]
theorem treeEq0353 : B0353.tree = HexagonCover.NBand.M7100_7300.SplitData.node0353 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0354
  · rfl

def B0352 : Block := .branch 142 ![374144419156711147060143317175368453031918731002241, 1099511629314, 6148, 38685626227668133590622216, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), B0353, (.leaf 5 (Common.fact 150).pointIds 150), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq0352 : B0352.tree = HexagonCover.NBand.M7100_7300.SplitData.node0352 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0353
  · rfl
  · rfl

def B0351 : Block := .branch 144 ![374144419156711147060143317175368453031918731002241, 1099511629314, 6148, 38685626227668133590622216, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 134).pointIds 134), (.leaf 1 (Common.fact 135).pointIds 135), (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), B0352, (.leaf 6 (Common.fact 796).pointIds 796)]
theorem treeEq0351 : B0351.tree = HexagonCover.NBand.M7100_7300.SplitData.node0351 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0352
  · rfl

def B0350 : Block := .branch 68 ![374144419156711147060143317175368453031918731002241, 1099511629314, 6148, 38685626227668133590622216, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 794).pointIds 794), B0351, (.leaf 2 (Common.fact 681).pointIds 681), (.leaf 3 (Common.fact 682).pointIds 682), (.leaf 4 (Common.fact 683).pointIds 683), (.leaf 5 (Common.fact 684).pointIds 684), (.leaf 6 (Common.fact 795).pointIds 795)]
theorem treeEq0350 : B0350.tree = HexagonCover.NBand.M7100_7300.SplitData.node0350 := by
  change Tree.branch (68 : Fin 173) _ = Tree.branch (68 : Fin 173) _
  apply congrArg (Tree.branch (68 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0351
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0349 : Block := .branch 168 ![385, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974311749925714704515727424] ![B0350, (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq0349 : B0349.tree = HexagonCover.NBand.M7100_7300.SplitData.node0349 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0350
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0077 : Block := .branch 65 ![385, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257283796722853571625821405248] ![(.leaf 0 (Common.fact 122).pointIds 122), (.leaf 1 (Common.fact 123).pointIds 123), Tip0077_0078, (.leaf 3 (Common.fact 124).pointIds 124), (.leaf 4 (Common.fact 125).pointIds 125), (.leaf 5 (Common.fact 126).pointIds 126), B0349]
theorem treeEq0077 : B0077.tree = HexagonCover.NBand.M7100_7300.SplitData.node0077 := by
  change Tree.branch (65 : Fin 173) _ = Tree.branch (65 : Fin 173) _
  apply congrArg (Tree.branch (65 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0349

theorem accepted0077 : B0077.accepted = true := by decide +kernel
theorem checked0077 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0077 (maskNeeds ![385, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257283796722853571625821405248]) := by
  rw [← treeEq0077]
  exact B0077.sound accepted0077
#print axioms checked0077

def B0396 : Block := .branch 129 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 7496041897891979138949639723405976493363995296137280] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 298).pointIds 298), (.leaf 2 (Common.fact 299).pointIds 299), (.leaf 3 (Common.fact 300).pointIds 300), (.leaf 4 (Common.fact 565).pointIds 565), (.leaf 5 (Common.fact 301).pointIds 301), (.leaf 6 (Common.fact 820).pointIds 820)]
theorem treeEq0396 : B0396.tree = HexagonCover.NBand.M7100_7300.SplitData.node0396 := by
  change Tree.branch (129 : Fin 173) _ = Tree.branch (129 : Fin 173) _
  apply congrArg (Tree.branch (129 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0395 : Block := .branch 172 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 2993155358828875476113802322786877192417440224608272, 393248, 1509731191384600785987346648600081244853295600107584] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 818).pointIds 818), (.leaf 2 (Common.fact 819).pointIds 819), (.leaf 3 (Common.fact 663).pointIds 663), (.leaf 4 (Common.fact 769).pointIds 769), (.leaf 5 (Common.fact 702).pointIds 702), B0396]
theorem treeEq0395 : B0395.tree = HexagonCover.NBand.M7100_7300.SplitData.node0395 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0396

def B0394 : Block := .branch 171 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1509731191384600785987346648600081244853295600107584] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 815).pointIds 815), (.leaf 2 (Common.fact 816).pointIds 816), (.leaf 3 (Common.fact 658).pointIds 658), B0395, (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 817).pointIds 817)]
theorem treeEq0394 : B0394.tree = HexagonCover.NBand.M7100_7300.SplitData.node0394 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0395
  · rfl
  · rfl

def B0393 : Block := .branch 160 ![385, 906694508967996956870146, 18518801667747485700, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069142963767364961833639667564608] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 813).pointIds 813), (.leaf 2 (Common.fact 814).pointIds 814), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), B0394]
theorem treeEq0393 : B0393.tree = HexagonCover.NBand.M7100_7300.SplitData.node0393 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0394

def B0392 : Block := .branch 79 ![374144419156732414708075875829334913944883216515457, 302231599160682369517058, 18518801667747485700, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![(.leaf 0 (Common.fact 758).pointIds 758), B0393, (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), (.leaf 5 (Common.fact 224).pointIds 224), (.leaf 6 (Common.fact 759).pointIds 759)]
theorem treeEq0392 : B0392.tree = HexagonCover.NBand.M7100_7300.SplitData.node0392 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0393
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0391 : Block := .branch 124 ![374144419156711147060143317175368453031918731002241, 302231599160682369517058, 18518801667747485700, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![B0392, (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), (.leaf 4 (Common.fact 191).pointIds 191), (.leaf 5 (Common.fact 192).pointIds 192), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq0391 : B0391.tree = HexagonCover.NBand.M7100_7300.SplitData.node0391 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0392
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0390 : Block := .branch 168 ![385, 302231599160682369517058, 18518801667747485700, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1508269689747269883069143273252374783178708392345664] ![B0391, (.leaf 1 (Common.fact 807).pointIds 807), (.leaf 2 (Common.fact 808).pointIds 808), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq0390 : B0390.tree = HexagonCover.NBand.M7100_7300.SplitData.node0390 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0391
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0389 : Block := .branch 163 ![385, 302231599160682369517058, 18518801667747485700, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 539).pointIds 539), (.leaf 5 (Common.fact 248).pointIds 248), B0390]
theorem treeEq0389 : B0389.tree = HexagonCover.NBand.M7100_7300.SplitData.node0389 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0390

def B0388 : Block := .branch 165 ![385, 302231599160682369517058, 18518801667747485700, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 538).pointIds 538), B0389, (.leaf 0 [] 0)]
theorem treeEq0388 : B0388.tree = HexagonCover.NBand.M7100_7300.SplitData.node0388 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0389
  · rfl

def B0387 : Block := .branch 167 ![385, 302231599160682369517058, 18518801667747485700, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 532).pointIds 532), (.leaf 1 (Common.fact 533).pointIds 533), (.leaf 2 (Common.fact 534).pointIds 534), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 536).pointIds 536), B0388, (.leaf 6 (Common.fact 537).pointIds 537)]
theorem treeEq0387 : B0387.tree = HexagonCover.NBand.M7100_7300.SplitData.node0387 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0388
  · rfl

def B0386 : Block := .branch 142 ![385, 302231599160682369517058, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), B0387, (.leaf 5 (Common.fact 150).pointIds 150), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq0386 : B0386.tree = HexagonCover.NBand.M7100_7300.SplitData.node0386 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0387
  · rfl
  · rfl

def B0385 : Block := .branch 144 ![385, 302231599160682369517058, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 134).pointIds 134), (.leaf 1 (Common.fact 135).pointIds 135), (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), B0386, (.leaf 6 (Common.fact 754).pointIds 754)]
theorem treeEq0385 : B0385.tree = HexagonCover.NBand.M7100_7300.SplitData.node0385 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0386
  · rfl

def B0384 : Block := .branch 170 ![385, 302231599160682369517058, 18518801667747485700, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 21778071482940525889170706893786007994432] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 811).pointIds 811), (.leaf 2 (Common.fact 812).pointIds 812), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 528).pointIds 528), (.leaf 5 (Common.fact 529).pointIds 529), B0385]
theorem treeEq0384 : B0384.tree = HexagonCover.NBand.M7100_7300.SplitData.node0384 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0385

def B0400 : Block := .branch 161 ![385, 1538, 18518801667747485700, 1496577676626844588240573307387100039795808514629640, 98320, 393248, 5986310706529156424445550435973870557418592698630208] ![(.leaf 0 (Common.fact 331).pointIds 331), (.leaf 1 (Common.fact 332).pointIds 332), (.leaf 2 (Common.fact 821).pointIds 821), (.leaf 3 (Common.fact 667).pointIds 667), (.leaf 4 (Common.fact 333).pointIds 333), (.leaf 5 (Common.fact 334).pointIds 334), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq0400 : B0400.tree = HexagonCover.NBand.M7100_7300.SplitData.node0400 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0399 : Block := .branch 170 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 5986310706529156424445550435973870557418592698630208] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 811).pointIds 811), (.leaf 2 (Common.fact 812).pointIds 812), B0400, (.leaf 4 (Common.fact 528).pointIds 528), (.leaf 5 (Common.fact 529).pointIds 529), (.leaf 6 (Common.fact 666).pointIds 666)]
theorem treeEq0399 : B0399.tree = HexagonCover.NBand.M7100_7300.SplitData.node0399 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0400
  · rfl
  · rfl
  · rfl

def B0398 : Block := .branch 172 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257361167975308907893002600512] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 818).pointIds 818), (.leaf 2 (Common.fact 819).pointIds 819), (.leaf 3 (Common.fact 663).pointIds 663), (.leaf 4 (Common.fact 743).pointIds 743), (.leaf 5 (Common.fact 702).pointIds 702), B0399]
theorem treeEq0398 : B0398.tree = HexagonCover.NBand.M7100_7300.SplitData.node0398 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0399

def B0397 : Block := .branch 171 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257361167975308907893002600512] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 815).pointIds 815), (.leaf 2 (Common.fact 816).pointIds 816), (.leaf 3 (Common.fact 658).pointIds 658), B0398, (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 660).pointIds 660)]
theorem treeEq0397 : B0397.tree = HexagonCover.NBand.M7100_7300.SplitData.node0397 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0398
  · rfl
  · rfl

def B0383 : Block := .branch 86 ![385, 302231599160682369517058, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 326).pointIds 326), (.leaf 1 (Common.fact 327).pointIds 327), (.leaf 2 (Common.fact 328).pointIds 328), B0384, (.leaf 4 (Common.fact 329).pointIds 329), (.leaf 5 (Common.fact 330).pointIds 330), B0397]
theorem treeEq0383 : B0383.tree = HexagonCover.NBand.M7100_7300.SplitData.node0383 := by
  change Tree.branch (86 : Fin 173) _ = Tree.branch (86 : Fin 173) _
  apply congrArg (Tree.branch (86 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0384
  · rfl
  · rfl
  · exact treeEq0397

theorem accepted0383 : B0383.accepted = true := by decide +kernel
theorem checked0383 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0383 (maskNeeds ![385, 302231599160682369517058, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0383]
  exact B0383.sound accepted0383
#print axioms checked0383

def B0439 : Block := .branch 79 ![374144419156732414710611177030381668558235328577921, 730750818665451459101842416358141510927477900802, 6148, 24584, 98320, 393248, 32667107224727005218098883390288002809920] ![(.leaf 0 (Common.fact 716).pointIds 716), (.leaf 1 (Common.fact 717).pointIds 717), (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), (.leaf 5 (Common.fact 224).pointIds 224), (.leaf 6 (Common.fact 718).pointIds 718)]
theorem treeEq0439 : B0439.tree = HexagonCover.NBand.M7100_7300.SplitData.node0439 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0438 : Block := .branch 159 ![374144419156732414710611177030381668558235328577921, 1099511629314, 6148, 24584, 98320, 393248, 5986310706545489978057755095439408125619895990222912] ![(.leaf 0 (Common.fact 714).pointIds 714), B0439, (.leaf 2 (Common.fact 228).pointIds 228), (.leaf 3 (Common.fact 229).pointIds 229), (.leaf 4 (Common.fact 230).pointIds 230), (.leaf 5 (Common.fact 231).pointIds 231), (.leaf 6 (Common.fact 715).pointIds 715)]
theorem treeEq0438 : B0438.tree = HexagonCover.NBand.M7100_7300.SplitData.node0438 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0439
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0437 : Block := .branch 124 ![374144419156711147062678618376415207645270843064705, 1099511629314, 6148, 24584, 98320, 393248, 5986310706545489978057755095439408125619895990222912] ![B0438, (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), (.leaf 4 (Common.fact 191).pointIds 191), (.leaf 5 (Common.fact 192).pointIds 192), (.leaf 6 (Common.fact 713).pointIds 713)]
theorem treeEq0437 : B0437.tree = HexagonCover.NBand.M7100_7300.SplitData.node0437 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0438
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0436 : Block := .branch 128 ![374144419156711147062678618376415207645270843064705, 1099511629314, 6148, 24584, 185542200051774784537577176028434367729757159440, 393248, 5986310706545489978057755095439408125619895990222912] ![(.leaf 0 (Common.fact 261).pointIds 261), (.leaf 1 (Common.fact 262).pointIds 262), (.leaf 2 (Common.fact 263).pointIds 263), B0437, (.leaf 4 (Common.fact 711).pointIds 711), (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 712).pointIds 712)]
theorem treeEq0436 : B0436.tree = HexagonCover.NBand.M7100_7300.SplitData.node0436 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0437
  · rfl
  · rfl
  · rfl

def B0435 : Block := .branch 138 ![374144419156711147062678618376415207645270843064705, 1099511629314, 6148, 38685626227668133590622216, 185542200051774784537577176028434367729757159440, 393248, 7482888383172334566298328364140881937747570914230336] ![(.leaf 0 (Common.fact 116).pointIds 116), (.leaf 1 (Common.fact 117).pointIds 117), (.leaf 2 (Common.fact 118).pointIds 118), (.leaf 3 (Common.fact 119).pointIds 119), B0436, (.leaf 5 (Common.fact 120).pointIds 120), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq0435 : B0435.tree = HexagonCover.NBand.M7100_7300.SplitData.node0435 := by
  change Tree.branch (138 : Fin 173) _ = Tree.branch (138 : Fin 173) _
  apply congrArg (Tree.branch (138 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0436
  · rfl
  · rfl

def B0434 : Block := .branch 139 ![374144419156711147062678618376415207645270843064705, 1099511629314, 6148, 38685626227668133590622216, 185542200051774784537577176028434367729757159440, 393248, 7482888383172334566298328364140881937747570914230336] ![(.leaf 0 (Common.fact 110).pointIds 110), (.leaf 1 (Common.fact 111).pointIds 111), (.leaf 2 (Common.fact 112).pointIds 112), (.leaf 3 (Common.fact 113).pointIds 113), B0435, (.leaf 5 (Common.fact 114).pointIds 114), (.leaf 6 (Common.fact 844).pointIds 844)]
theorem treeEq0434 : B0434.tree = HexagonCover.NBand.M7100_7300.SplitData.node0434 := by
  change Tree.branch (139 : Fin 173) _ = Tree.branch (139 : Fin 173) _
  apply congrArg (Tree.branch (139 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0435
  · rfl
  · rfl

def B0433 : Block := .branch 140 ![374144419156711147062678618376415207645270843064705, 1099511629314, 6148, 38685626227668133590622216, 185542200051774784537577176028434367729757159440, 393248, 7482888383172334566298328364140881937747570914230336] ![(.leaf 0 (Common.fact 104).pointIds 104), (.leaf 1 (Common.fact 105).pointIds 105), (.leaf 2 (Common.fact 106).pointIds 106), (.leaf 3 (Common.fact 107).pointIds 107), B0434, (.leaf 5 (Common.fact 108).pointIds 108), (.leaf 6 (Common.fact 843).pointIds 843)]
theorem treeEq0433 : B0433.tree = HexagonCover.NBand.M7100_7300.SplitData.node0433 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0434
  · rfl
  · rfl

def B0432 : Block := .branch 141 ![374144419156711147062678618376415207645270843064705, 1099511629314, 6148, 38685626227668133590622216, 185542200051774784537577176028434367729757159440, 393248, 7482888383172334566298328364140881937747570914230336] ![(.leaf 0 (Common.fact 98).pointIds 98), (.leaf 1 (Common.fact 99).pointIds 99), (.leaf 2 (Common.fact 100).pointIds 100), (.leaf 3 (Common.fact 101).pointIds 101), B0433, (.leaf 5 (Common.fact 102).pointIds 102), (.leaf 6 (Common.fact 842).pointIds 842)]
theorem treeEq0432 : B0432.tree = HexagonCover.NBand.M7100_7300.SplitData.node0432 := by
  change Tree.branch (141 : Fin 173) _ = Tree.branch (141 : Fin 173) _
  apply congrArg (Tree.branch (141 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0433
  · rfl
  · rfl

def B0431 : Block := .branch 142 ![374144419156711147062678618376415207645270843064705, 1099511629314, 6148, 38685626227668133590622216, 185542200051774784537577176028434367729757159440, 393248, 7482888383172334566298328364140881937747570914230336] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), B0432, (.leaf 5 (Common.fact 150).pointIds 150), (.leaf 6 (Common.fact 841).pointIds 841)]
theorem treeEq0431 : B0431.tree = HexagonCover.NBand.M7100_7300.SplitData.node0431 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0432
  · rfl
  · rfl

def B0430 : Block := .branch 165 ![374144419156711147062678618376415207645270843064705, 1099511629314, 6148, 38685626227668133590622216, 185553350424374049849147943887570691910510149648, 393248, 7482888383172334566298328364140881937747570914230336] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 840).pointIds 840), B0431, (.leaf 0 [] 0)]
theorem treeEq0430 : B0430.tree = HexagonCover.NBand.M7100_7300.SplitData.node0430 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0431
  · rfl

def B0429 : Block := .branch 167 ![374144419156711147062678618376415207645270843064705, 1099511629314, 6148, 38685626227668133590622216, 185553350424374049849147943887570691910510149648, 393248, 7482888383172334566298328364140881937747570914230336] ![(.leaf 0 (Common.fact 532).pointIds 532), (.leaf 1 (Common.fact 533).pointIds 533), (.leaf 2 (Common.fact 534).pointIds 534), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 839).pointIds 839), B0430, (.leaf 6 (Common.fact 537).pointIds 537)]
theorem treeEq0429 : B0429.tree = HexagonCover.NBand.M7100_7300.SplitData.node0429 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0430
  · rfl

def B0428 : Block := .branch 143 ![374144419156711147062678618376415207645270843064705, 1099511629314, 6148, 38685626227668133590622216, 185542200051774784537577176028434367729757159440, 748288838313422294120286634350736906063837462396960, 7482888383172334566298328364140881937747570914230336] ![(.leaf 0 (Common.fact 427).pointIds 427), (.leaf 1 (Common.fact 428).pointIds 428), (.leaf 2 (Common.fact 429).pointIds 429), (.leaf 3 (Common.fact 430).pointIds 430), B0429, (.leaf 5 (Common.fact 837).pointIds 837), (.leaf 6 (Common.fact 838).pointIds 838)]
theorem treeEq0428 : B0428.tree = HexagonCover.NBand.M7100_7300.SplitData.node0428 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0429
  · rfl
  · rfl

def B0427 : Block := .branch 170 ![374144419156711147062678618376415207645270843064705, 144257025075840514, 18518801667747485700, 8769009823985417509222147681923925786069185880072, 186255823898127764478106319013159115297948532752, 748288838313422294120286634350736906063837462396960, 5986310706545489978057755095439408125619895990222912] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 811).pointIds 811), (.leaf 2 (Common.fact 812).pointIds 812), (.leaf 3 (Common.fact 836).pointIds 836), (.leaf 4 (Common.fact 528).pointIds 528), (.leaf 5 (Common.fact 529).pointIds 529), B0428]
theorem treeEq0427 : B0427.tree = HexagonCover.NBand.M7100_7300.SplitData.node0427 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0428

def B0426 : Block := .branch 161 ![374144419156711147062678618376415207645270843064705, 144257025075840514, 18518801667747485700, 5846006549323611672814778016491359746757320794120, 186255823898127764478106319013159115297948532752, 748288838313422294120286634350736906063837462396960, 5986310706545489978057755095439408125619895990222912] ![(.leaf 0 (Common.fact 331).pointIds 331), (.leaf 1 (Common.fact 332).pointIds 332), (.leaf 2 (Common.fact 821).pointIds 821), B0427, (.leaf 4 (Common.fact 333).pointIds 333), (.leaf 5 (Common.fact 334).pointIds 334), (.leaf 6 (Common.fact 835).pointIds 835)]
theorem treeEq0426 : B0426.tree = HexagonCover.NBand.M7100_7300.SplitData.node0426 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0427
  · rfl
  · rfl
  · rfl

def B0425 : Block := .branch 75 ![374144419156711147062678618376415207645270843064705, 144257025075840514, 18518801667747485700, 5846006549323611672814778016491359746757320794120, 186255823898127764478106319013159115297948532752, 748288838313422294120286634350736906063837462396960, 5986310706545489978057755095439408125619895990222912] ![(.leaf 0 (Common.fact 705).pointIds 705), (.leaf 1 (Common.fact 706).pointIds 706), B0426, (.leaf 3 (Common.fact 707).pointIds 707), (.leaf 4 (Common.fact 708).pointIds 708), (.leaf 5 (Common.fact 709).pointIds 709), (.leaf 6 (Common.fact 710).pointIds 710)]
theorem treeEq0425 : B0425.tree = HexagonCover.NBand.M7100_7300.SplitData.node0425 := by
  change Tree.branch (75 : Fin 173) _ = Tree.branch (75 : Fin 173) _
  apply congrArg (Tree.branch (75 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0426
  · rfl
  · rfl
  · rfl
  · rfl

def B0424 : Block := .branch 162 ![374144419156711147062678618376415207645270843064705, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 186255823898127764478106319013159115297948532752, 748288838313422294120286634350736906063837462396960, 5986310706545489978057755095439408125619895990222912] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), B0425, (.leaf 4 (Common.fact 703).pointIds 703), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 704).pointIds 704)]
theorem treeEq0424 : B0424.tree = HexagonCover.NBand.M7100_7300.SplitData.node0424 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0425
  · rfl
  · rfl
  · rfl

def B0423 : Block := .branch 172 ![374144419156711147062678618376415207645270843064705, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 186255823898127764478106319013159115297948532752, 748288838313422294120286634350736906063837462396960, 38111625095462020633512877109196294193216] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 818).pointIds 818), (.leaf 2 (Common.fact 819).pointIds 819), (.leaf 3 (Common.fact 663).pointIds 663), (.leaf 4 (Common.fact 701).pointIds 701), (.leaf 5 (Common.fact 702).pointIds 702), B0424]
theorem treeEq0423 : B0423.tree = HexagonCover.NBand.M7100_7300.SplitData.node0423 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0424

def B0422 : Block := .branch 151 ![374144419156711147062678618376415207645270843064705, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 748288838313422294120286634350736906063837462396960, 38111625095462020633512877109196294193216] ![(.leaf 0 (Common.fact 250).pointIds 250), (.leaf 1 (Common.fact 251).pointIds 251), (.leaf 2 (Common.fact 252).pointIds 252), (.leaf 3 (Common.fact 253).pointIds 253), B0423, (.leaf 5 (Common.fact 696).pointIds 696), (.leaf 6 (Common.fact 697).pointIds 697)]
theorem treeEq0422 : B0422.tree = HexagonCover.NBand.M7100_7300.SplitData.node0422 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0423
  · rfl
  · rfl

def B0421 : Block := .branch 132 ![374144419156711147062678618376415207645270843064705, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 748288838313422294120286634350736906063837462396960, 32667107224727005218098883390288002809920] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 695).pointIds 695), (.leaf 5 (Common.fact 219).pointIds 219), B0422]
theorem treeEq0421 : B0421.tree = HexagonCover.NBand.M7100_7300.SplitData.node0421 := by
  change Tree.branch (132 : Fin 173) _ = Tree.branch (132 : Fin 173) _
  apply congrArg (Tree.branch (132 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0422

def B0420 : Block := .branch 78 ![374144419156711147062678618376415207645270843064705, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 748288838313422294120286634350736906063837462396960, 32667107224727005218098883390288002809920] ![(.leaf 0 (Common.fact 140).pointIds 140), B0421, (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), (.leaf 4 (Common.fact 144).pointIds 144), (.leaf 5 (Common.fact 145).pointIds 145), (.leaf 6 (Common.fact 694).pointIds 694)]
theorem treeEq0420 : B0420.tree = HexagonCover.NBand.M7100_7300.SplitData.node0420 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0421
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0420 : B0420.accepted = true := by decide +kernel
theorem checked0420 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0420 (maskNeeds ![374144419156711147062678618376415207645270843064705, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 748288838313422294120286634350736906063837462396960, 32667107224727005218098883390288002809920]) := by
  rw [← treeEq0420]
  exact B0420.sound accepted0420
#print axioms checked0420

def Tip0411_0420 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0420 ![374144419156711147062678618376415207645270843064705, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 748288838313422294120286634350736906063837462396960, 32667107224727005218098883390288002809920] checked0420
def B0419 : Block := .branch 101 ![374144419156711147060143317175958748842277436653953, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 748288838313422294120286634350736906063837462396960, 32667107224727005218098883390288002809920] ![Tip0411_0420, (.leaf 1 (Common.fact 408).pointIds 408), (.leaf 2 (Common.fact 409).pointIds 409), (.leaf 3 (Common.fact 410).pointIds 410), (.leaf 4 (Common.fact 411).pointIds 411), (.leaf 5 (Common.fact 412).pointIds 412), (.leaf 6 (Common.fact 693).pointIds 693)]
theorem treeEq0419 : B0419.tree = HexagonCover.NBand.M7100_7300.SplitData.node0419 := by
  change Tree.branch (101 : Fin 173) _ = Tree.branch (101 : Fin 173) _
  apply congrArg (Tree.branch (101 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0418 : Block := .branch 168 ![590295810358705652097, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 748288838313422294120286634350736906063837462396960, 32667107224727005218098883390288002809920] ![B0419, (.leaf 1 (Common.fact 807).pointIds 807), (.leaf 2 (Common.fact 808).pointIds 808), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 692).pointIds 692)]
theorem treeEq0418 : B0418.tree = HexagonCover.NBand.M7100_7300.SplitData.node0418 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0419
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0417 : Block := .branch 133 ![590295810358705652097, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 748288838313422294120286634350736906063837462396960, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), (.leaf 4 (Common.fact 691).pointIds 691), (.leaf 5 (Common.fact 212).pointIds 212), B0418]
theorem treeEq0417 : B0417.tree = HexagonCover.NBand.M7100_7300.SplitData.node0417 := by
  change Tree.branch (133 : Fin 173) _ = Tree.branch (133 : Fin 173) _
  apply congrArg (Tree.branch (133 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0418

def B0416 : Block := .branch 157 ![590295810358705652097, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 748288838313422294120286634350736906063837462396960, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 202).pointIds 202), (.leaf 1 (Common.fact 203).pointIds 203), (.leaf 2 (Common.fact 204).pointIds 204), (.leaf 3 (Common.fact 205).pointIds 205), B0417, (.leaf 5 (Common.fact 484).pointIds 484), (.leaf 0 [] 0)]
theorem treeEq0416 : B0416.tree = HexagonCover.NBand.M7100_7300.SplitData.node0416 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0417
  · rfl
  · rfl

def B0415 : Block := .branch 169 ![10384593717070245552871351364092289, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 686).pointIds 686), (.leaf 1 (Common.fact 825).pointIds 825), (.leaf 2 (Common.fact 826).pointIds 826), (.leaf 3 (Common.fact 689).pointIds 689), (.leaf 4 (Common.fact 571).pointIds 571), B0416, (.leaf 6 (Common.fact 690).pointIds 690)]
theorem treeEq0415 : B0415.tree = HexagonCover.NBand.M7100_7300.SplitData.node0415 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0416
  · rfl

def B0448 : Block := .branch 124 ![730750818665461843695559486013398570820624712065, 1538, 6148, 24584, 98320, 393248, 5987772208166487327363753734025882427482827048616000] ![(.leaf 0 (Common.fact 855).pointIds 855), (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), (.leaf 4 (Common.fact 191).pointIds 191), (.leaf 5 (Common.fact 192).pointIds 192), (.leaf 6 (Common.fact 856).pointIds 856)]
theorem treeEq0448 : B0448.tree = HexagonCover.NBand.M7100_7300.SplitData.node0448 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0447 : Block := .branch 159 ![10384593717069655257060992658440577, 737869904785382049282, 6148, 24584, 98320, 393248, 5987772208166487327363753734025882427482827048616000] ![B0448, (.leaf 1 (Common.fact 853).pointIds 853), (.leaf 2 (Common.fact 228).pointIds 228), (.leaf 3 (Common.fact 229).pointIds 229), (.leaf 4 (Common.fact 230).pointIds 230), (.leaf 5 (Common.fact 231).pointIds 231), (.leaf 6 (Common.fact 854).pointIds 854)]
theorem treeEq0447 : B0447.tree = HexagonCover.NBand.M7100_7300.SplitData.node0447 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0448
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0446 : Block := .branch 75 ![10384593717069655257060992658440577, 737869904785382049282, 6148, 2923003274661805836407369665432566039311865110536, 98320, 393248, 5987772208166487327363753734025882427482827048616000] ![(.leaf 0 (Common.fact 705).pointIds 705), (.leaf 1 (Common.fact 706).pointIds 706), B0447, (.leaf 3 (Common.fact 851).pointIds 851), (.leaf 4 (Common.fact 708).pointIds 708), (.leaf 5 (Common.fact 709).pointIds 709), (.leaf 6 (Common.fact 852).pointIds 852)]
theorem treeEq0446 : B0446.tree = HexagonCover.NBand.M7100_7300.SplitData.node0446 := by
  change Tree.branch (75 : Fin 173) _ = Tree.branch (75 : Fin 173) _
  apply congrArg (Tree.branch (75 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0447
  · rfl
  · rfl
  · rfl
  · rfl

def B0445 : Block := .branch 170 ![10384593717069655257060992658440577, 738014019973457905154, 18518801667747485700, 2923003274661805836407369665432566039311865110536, 713623846352979940529142984724747568191471632, 393248, 5987772208166487327363753734025882427482827048616000] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 811).pointIds 811), (.leaf 2 (Common.fact 812).pointIds 812), (.leaf 3 (Common.fact 850).pointIds 850), (.leaf 4 (Common.fact 528).pointIds 528), (.leaf 5 (Common.fact 529).pointIds 529), B0446]
theorem treeEq0445 : B0445.tree = HexagonCover.NBand.M7100_7300.SplitData.node0445 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0446

def B0444 : Block := .branch 161 ![10384593717069655257060992658440577, 738014019973457905154, 18518801667747485700, 24584, 713623846352979940529142984724747568191471632, 393248, 5987772208166487327363753734025882427482827048616000] ![(.leaf 0 (Common.fact 331).pointIds 331), (.leaf 1 (Common.fact 332).pointIds 332), (.leaf 2 (Common.fact 821).pointIds 821), B0445, (.leaf 4 (Common.fact 333).pointIds 333), (.leaf 5 (Common.fact 334).pointIds 334), (.leaf 6 (Common.fact 849).pointIds 849)]
theorem treeEq0444 : B0444.tree = HexagonCover.NBand.M7100_7300.SplitData.node0444 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0445
  · rfl
  · rfl
  · rfl

def B0443 : Block := .branch 168 ![10384593717069655257060992658440577, 738014019973457905154, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 5987772208166487327363753734025882427482827048616000] ![B0444, (.leaf 1 (Common.fact 807).pointIds 807), (.leaf 2 (Common.fact 808).pointIds 808), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 848).pointIds 848)]
theorem treeEq0443 : B0443.tree = HexagonCover.NBand.M7100_7300.SplitData.node0443 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0444
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0442 : Block := .branch 172 ![10384593717069655257060992658440577, 738014019973457905154, 18518801667747485700, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 1461501659108974401460659219987178972127352586304] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 818).pointIds 818), (.leaf 2 (Common.fact 819).pointIds 819), (.leaf 3 (Common.fact 663).pointIds 663), (.leaf 4 (Common.fact 743).pointIds 743), (.leaf 5 (Common.fact 702).pointIds 702), B0443]
theorem treeEq0442 : B0442.tree = HexagonCover.NBand.M7100_7300.SplitData.node0442 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0443

def B0441 : Block := .branch 171 ![10384593717069655257060992658440577, 738014019973457905154, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 1461501659108974401460659219987178972127352586304] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 815).pointIds 815), (.leaf 2 (Common.fact 816).pointIds 816), (.leaf 3 (Common.fact 658).pointIds 658), B0442, (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq0441 : B0441.tree = HexagonCover.NBand.M7100_7300.SplitData.node0441 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0442
  · rfl
  · rfl

def B0440 : Block := .branch 160 ![10384593717069655257060992658440577, 738014019973457905154, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 846).pointIds 846), (.leaf 2 (Common.fact 814).pointIds 814), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), B0441]
theorem treeEq0440 : B0440.tree = HexagonCover.NBand.M7100_7300.SplitData.node0440 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0441

def B0414 : Block := .branch 69 ![10384593717069655257060992658440577, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![B0415, B0440, (.leaf 2 (Common.fact 421).pointIds 421), (.leaf 3 (Common.fact 422).pointIds 422), (.leaf 4 (Common.fact 423).pointIds 423), (.leaf 5 (Common.fact 424).pointIds 424), (.leaf 6 (Common.fact 685).pointIds 685)]
theorem treeEq0414 : B0414.tree = HexagonCover.NBand.M7100_7300.SplitData.node0414 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0415
  · exact treeEq0440
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0450 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 21778071483256974387566043857650772869184] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 749).pointIds 749), (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 750).pointIds 750)]
theorem treeEq0450 : B0450.tree = HexagonCover.NBand.M7100_7300.SplitData.node0450 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0449 : Block := .branch 172 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 98320, 393248, 21778071483256974387566043857650772869184] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 818).pointIds 818), (.leaf 2 (Common.fact 819).pointIds 819), (.leaf 3 (Common.fact 663).pointIds 663), B0450, (.leaf 5 (Common.fact 702).pointIds 702), (.leaf 6 (Common.fact 748).pointIds 748)]
theorem treeEq0449 : B0449.tree = HexagonCover.NBand.M7100_7300.SplitData.node0449 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0450
  · rfl
  · rfl

def B0413 : Block := .branch 68 ![10384593717069655257060992658440577, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 680).pointIds 680), B0414, (.leaf 2 (Common.fact 681).pointIds 681), (.leaf 3 (Common.fact 682).pointIds 682), (.leaf 4 (Common.fact 683).pointIds 683), (.leaf 5 (Common.fact 684).pointIds 684), B0449]
theorem treeEq0413 : B0413.tree = HexagonCover.NBand.M7100_7300.SplitData.node0413 := by
  change Tree.branch (68 : Fin 173) _ = Tree.branch (68 : Fin 173) _
  apply congrArg (Tree.branch (68 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0414
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0449

def B0412 : Block := .branch 91 ![10384593717069655257060992658440577, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![B0413, (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 320).pointIds 320), (.leaf 5 (Common.fact 321).pointIds 321), (.leaf 6 (Common.fact 679).pointIds 679)]
theorem treeEq0412 : B0412.tree = HexagonCover.NBand.M7100_7300.SplitData.node0412 := by
  change Tree.branch (91 : Fin 173) _ = Tree.branch (91 : Fin 173) _
  apply congrArg (Tree.branch (91 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0413
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0411 : Block := .branch 113 ![385, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![B0412, (.leaf 1 (Common.fact 239).pointIds 239), (.leaf 2 (Common.fact 240).pointIds 240), (.leaf 3 (Common.fact 241).pointIds 241), (.leaf 4 (Common.fact 242).pointIds 242), (.leaf 5 (Common.fact 243).pointIds 243), (.leaf 6 (Common.fact 678).pointIds 678)]
theorem treeEq0411 : B0411.tree = HexagonCover.NBand.M7100_7300.SplitData.node0411 := by
  change Tree.branch (113 : Fin 173) _ = Tree.branch (113 : Fin 173) _
  apply congrArg (Tree.branch (113 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0412
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0411 : B0411.accepted = true := by decide +kernel
theorem checked0411 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0411 (maskNeeds ![385, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328]) := by
  rw [← treeEq0411]
  exact B0411.sound accepted0411
#print axioms checked0411

end HexagonCover.NBand.M7100_7300.SplitTree.Run0004
