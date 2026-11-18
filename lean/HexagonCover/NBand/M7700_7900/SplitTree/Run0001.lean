import HexagonCover.NBand.M7700_7900.SplitData
import HexagonCover.NBand.M7700_7900.SplitTree.Run0000
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7700_7900.SplitTree.Run0001
open OwnerTree HexagonCover.NBand.M7700_7900

abbrev Block := Chunk (n := 172) (Certificate := Fin 836) (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck

def Tip0138_0143 : Block := .tip HexagonCover.NBand.M7700_7900.SplitData.node0143 ![1267650600228229401496703205761, 453347182355485940516354, 77937529740219874547716, 174224571863520609350126482009466096082952, 11874879209275174779908625209992707504752520429584, 42535295865117307932921825928971419680, 2854522629268921687129180547117866305726185536] HexagonCover.NBand.M7700_7900.SplitTree.Run0000.checked0143
def B0162 : Block := .branch 170 ![374144419156711147061410967775596682433415434207617, 1461501637330902918203685134947737923313226221058, 153476910693263469451268, 2923003448886377699927862958680365044377189376008, 11874700803313586534923492924246526317860472586256, 42535295865117307932921825928971419680, 2854517184751050952113765133124147397434802240] ![(.leaf 0 (Common.fact 542).pointIds 542), (.leaf 1 (Common.fact 543).pointIds 543), (.leaf 2 (Common.fact 544).pointIds 544), (.leaf 3 (Common.fact 534).pointIds 534), (.leaf 4 (Common.fact 529).pointIds 529), (.leaf 5 (Common.fact 525).pointIds 525), (.leaf 6 (Common.fact 526).pointIds 526)]
theorem treeEq0162 : B0162.tree = HexagonCover.NBand.M7700_7900.SplitData.node0162 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0161 : Block := .branch 168 ![1267650600228229401496703205761, 1461501637330902918203685134947737923313226221058, 153495393466134197966852, 2923003448886377699927901644306592712510779973640, 11874879209275174779908625209992707504752520429584, 42535295865117307932921825928971419680, 2854522629268921687129180547117866305726185536] ![B0162, (.leaf 1 (Common.fact 385).pointIds 385), (.leaf 2 (Common.fact 512).pointIds 512), (.leaf 3 (Common.fact 513).pointIds 513), (.leaf 4 (Common.fact 514).pointIds 514), (.leaf 5 (Common.fact 515).pointIds 515), (.leaf 6 (Common.fact 516).pointIds 516)]
theorem treeEq0161 : B0161.tree = HexagonCover.NBand.M7700_7900.SplitData.node0161 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0162
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0160 : Block := .branch 160 ![1267650600228229401496703205761, 302231454903657293678082, 153495393466134197966852, 2923003448886377699927901644306592712510779973640, 11874879209275174779908625209992707504752520429584, 42535295865117307932921825928971419680, 2854522629268921687129180547117866305726185536] ![(.leaf 0 (Common.fact 365).pointIds 365), B0161, (.leaf 2 (Common.fact 416).pointIds 416), (.leaf 3 (Common.fact 366).pointIds 366), (.leaf 4 (Common.fact 367).pointIds 367), (.leaf 5 (Common.fact 368).pointIds 368), (.leaf 6 (Common.fact 510).pointIds 510)]
theorem treeEq0160 : B0160.tree = HexagonCover.NBand.M7700_7900.SplitData.node0160 := by
  change Tree.branch (160 : Fin 172) _ = Tree.branch (160 : Fin 172) _
  apply congrArg (Tree.branch (160 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0161
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0159 : Block := .branch 161 ![1267650600228229401496703205761, 302231454903657293678082, 153495393466134197966852, 174224571863520531978874026673198914887688, 11874879209275174779908625209992707504752520429584, 42535295865117307932921825928971419680, 2854522629268921687129180547117866305726185536] ![(.leaf 0 (Common.fact 370).pointIds 370), (.leaf 1 (Common.fact 371).pointIds 371), (.leaf 2 (Common.fact 415).pointIds 415), B0160, (.leaf 4 (Common.fact 372).pointIds 372), (.leaf 5 (Common.fact 373).pointIds 373), (.leaf 6 (Common.fact 517).pointIds 517)]
theorem treeEq0159 : B0159.tree = HexagonCover.NBand.M7700_7900.SplitData.node0159 := by
  change Tree.branch (161 : Fin 172) _ = Tree.branch (161 : Fin 172) _
  apply congrArg (Tree.branch (161 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0160
  · rfl
  · rfl
  · rfl

def B0142 : Block := .branch 77 ![1267650600228229401496703205761, 302231454903657293678082, 77937529740219874547716, 174224571863520609350126482009466096082952, 11874879209275174779908625209992707504752520429584, 42535295865117307932921825928971419680, 2854522629268921687129180547117866305726185536] ![(.leaf 0 (Common.fact 355).pointIds 355), Tip0138_0143, B0159, (.leaf 3 (Common.fact 356).pointIds 356), (.leaf 4 (Common.fact 357).pointIds 357), (.leaf 5 (Common.fact 358).pointIds 358), (.leaf 6 (Common.fact 499).pointIds 499)]
theorem treeEq0142 : B0142.tree = HexagonCover.NBand.M7700_7900.SplitData.node0142 := by
  change Tree.branch (77 : Fin 172) _ = Tree.branch (77 : Fin 172) _
  apply congrArg (Tree.branch (77 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0159
  · rfl
  · rfl
  · rfl
  · rfl

def B0166 : Block := .branch 170 ![374144419156711147061410967775596682433415434207617, 1461501637330902918203685134947737923313226221058, 77992833943643984238596, 2923003448886377699927862958680365044377189376008, 11874700803313586534923492924246526317860472586256, 42535295865117307932921825928971419680, 2854517184751050952113765133124147397434802240] ![(.leaf 0 (Common.fact 542).pointIds 542), (.leaf 1 (Common.fact 543).pointIds 543), (.leaf 2 (Common.fact 547).pointIds 547), (.leaf 3 (Common.fact 534).pointIds 534), (.leaf 4 (Common.fact 529).pointIds 529), (.leaf 5 (Common.fact 525).pointIds 525), (.leaf 6 (Common.fact 526).pointIds 526)]
theorem treeEq0166 : B0166.tree = HexagonCover.NBand.M7700_7900.SplitData.node0166 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0165 : Block := .branch 168 ![1267650600228229401496703205761, 1461501637330902918203685134947737923313226221058, 78011316716514712754180, 2923003448886377699927901644306592712510779973640, 11874879209275174779908625209992707504752520429584, 42535295865117307932921825928971419680, 2854522629268921687129180547117866305726185536] ![B0166, (.leaf 1 (Common.fact 385).pointIds 385), (.leaf 2 (Common.fact 512).pointIds 512), (.leaf 3 (Common.fact 513).pointIds 513), (.leaf 4 (Common.fact 514).pointIds 514), (.leaf 5 (Common.fact 515).pointIds 515), (.leaf 6 (Common.fact 516).pointIds 516)]
theorem treeEq0165 : B0165.tree = HexagonCover.NBand.M7700_7900.SplitData.node0165 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0166
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0164 : Block := .branch 160 ![1267650600228229401496703205761, 302231454903657293678082, 78011316716514712754180, 2923003448886377699927901644306592712510779973640, 11874879209275174779908625209992707504752520429584, 42535295865117307932921825928971419680, 2854522629268921687129180547117866305726185536] ![(.leaf 0 (Common.fact 365).pointIds 365), B0165, (.leaf 2 (Common.fact 546).pointIds 546), (.leaf 3 (Common.fact 366).pointIds 366), (.leaf 4 (Common.fact 367).pointIds 367), (.leaf 5 (Common.fact 368).pointIds 368), (.leaf 6 (Common.fact 510).pointIds 510)]
theorem treeEq0164 : B0164.tree = HexagonCover.NBand.M7700_7900.SplitData.node0164 := by
  change Tree.branch (160 : Fin 172) _ = Tree.branch (160 : Fin 172) _
  apply congrArg (Tree.branch (160 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0165
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0163 : Block := .branch 161 ![1267650600228229401496703205761, 302231454903657293678082, 78011316716514712754180, 174224571863520531978874026673198914887688, 11874879209275174779908625209992707504752520429584, 42535295865117307932921825928971419680, 2854522629268921687129180547117866305726185536] ![(.leaf 0 (Common.fact 370).pointIds 370), (.leaf 1 (Common.fact 371).pointIds 371), (.leaf 2 (Common.fact 545).pointIds 545), B0164, (.leaf 4 (Common.fact 372).pointIds 372), (.leaf 5 (Common.fact 373).pointIds 373), (.leaf 6 (Common.fact 517).pointIds 517)]
theorem treeEq0163 : B0163.tree = HexagonCover.NBand.M7700_7900.SplitData.node0163 := by
  change Tree.branch (161 : Fin 172) _ = Tree.branch (161 : Fin 172) _
  apply congrArg (Tree.branch (161 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0164
  · rfl
  · rfl
  · rfl

def B0141 : Block := .branch 66 ![1267650600228229401496703205761, 302231454903657293678082, 77937529740219874547716, 174224571863520609350126482009466096082952, 11874879209275174779908625209992707504752520429584, 42535295865117307932921825928971419680, 2854522629268921687129180547117866305726185536] ![(.leaf 0 (Common.fact 346).pointIds 346), B0142, B0163, (.leaf 3 (Common.fact 347).pointIds 347), (.leaf 4 (Common.fact 348).pointIds 348), (.leaf 5 (Common.fact 349).pointIds 349), (.leaf 6 (Common.fact 498).pointIds 498)]
theorem treeEq0141 : B0141.tree = HexagonCover.NBand.M7700_7900.SplitData.node0141 := by
  change Tree.branch (66 : Fin 172) _ = Tree.branch (66 : Fin 172) _
  apply congrArg (Tree.branch (66 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0142
  · exact treeEq0163
  · rfl
  · rfl
  · rfl
  · rfl

def B0140 : Block := .branch 137 ![1267650600228229401496703205761, 302231454903657293678082, 77937529740219874547716, 116056878683004400771817480, 11874879209275174779908625209992707504752520429584, 42535295865117307932921825928971419680, 2854522629268921687129180547117866305726185536] ![(.leaf 0 (Common.fact 293).pointIds 293), (.leaf 1 (Common.fact 294).pointIds 294), (.leaf 2 (Common.fact 295).pointIds 295), B0141, (.leaf 4 (Common.fact 296).pointIds 296), (.leaf 5 (Common.fact 297).pointIds 297), (.leaf 0 [] 0)]
theorem treeEq0140 : B0140.tree = HexagonCover.NBand.M7700_7900.SplitData.node0140 := by
  change Tree.branch (137 : Fin 172) _ = Tree.branch (137 : Fin 172) _
  apply congrArg (Tree.branch (137 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0141
  · rfl
  · rfl
  · rfl

def B0139 : Block := .branch 163 ![1267650600228229401496703205761, 302231454903657293678082, 77937529740219874547716, 116056878683004400771817480, 182866110627951434279146548262443347505060085776, 42535295865117307932921825928971419680, 2854522629268921687129180547117866305726185536] ![(.leaf 0 (Common.fact 287).pointIds 287), (.leaf 1 (Common.fact 288).pointIds 288), (.leaf 2 (Common.fact 289).pointIds 289), (.leaf 3 (Common.fact 290).pointIds 290), B0140, (.leaf 5 (Common.fact 291).pointIds 291), (.leaf 6 (Common.fact 497).pointIds 497)]
theorem treeEq0139 : B0139.tree = HexagonCover.NBand.M7700_7900.SplitData.node0139 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0140
  · rfl
  · rfl

def B0138 : Block := .branch 151 ![1267650600228229401496703205761, 302231454903657293678082, 77937529740219874547716, 116056878683004400771817480, 182866110627951434279146548262443347505060085776, 42535295865117307932921825928971419680, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 241).pointIds 241), (.leaf 1 (Common.fact 242).pointIds 242), (.leaf 2 (Common.fact 243).pointIds 243), (.leaf 3 (Common.fact 244).pointIds 244), (.leaf 4 (Common.fact 495).pointIds 495), (.leaf 5 (Common.fact 496).pointIds 496), B0139]
theorem treeEq0138 : B0138.tree = HexagonCover.NBand.M7700_7900.SplitData.node0138 := by
  change Tree.branch (151 : Fin 172) _ = Tree.branch (151 : Fin 172) _
  apply congrArg (Tree.branch (151 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0139

theorem accepted0138 : B0138.accepted = true := by decide +kernel
theorem checked0138 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7700_7900.SplitData.node0138 (maskNeeds ![1267650600228229401496703205761, 302231454903657293678082, 77937529740219874547716, 116056878683004400771817480, 182866110627951434279146548262443347505060085776, 42535295865117307932921825928971419680, 27243857001925012608608218876032960692288]) := by
  rw [← treeEq0138]
  exact B0138.sound accepted0138
#print axioms checked0138

def Tip0135_0138 : Block := .tip HexagonCover.NBand.M7700_7900.SplitData.node0138 ![1267650600228229401496703205761, 302231454903657293678082, 77937529740219874547716, 116056878683004400771817480, 182866110627951434279146548262443347505060085776, 42535295865117307932921825928971419680, 27243857001925012608608218876032960692288] checked0138
def B0176 : Block := .branch 170 ![10385861367669883486462489361645953, 302231526961251331606018, 77919046967349146032132, 5846006549323611672814816702117587414890911391752, 182699203488105857128017958444269711768393187344, 233840261972987002208454690542538204970878178295840, 22479903864714961470063917021614029930560] ![(.leaf 0 (Common.fact 562).pointIds 562), (.leaf 1 (Common.fact 563).pointIds 563), (.leaf 2 (Common.fact 533).pointIds 533), (.leaf 3 (Common.fact 564).pointIds 564), (.leaf 4 (Common.fact 565).pointIds 565), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 567).pointIds 567)]
theorem treeEq0176 : B0176.tree = HexagonCover.NBand.M7700_7900.SplitData.node0176 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0175 : Block := .branch 113 ![1267650600228229401496703205761, 302231526961251331606018, 77919046967349146032132, 5846006549323611672814816702117587414890911391752, 182699203488105857128017958444269711768393187344, 233840261972987002208454690542538204970878178295840, 27924422059968530543904637523678341890112] ![B0176, (.leaf 1 (Common.fact 180).pointIds 180), (.leaf 2 (Common.fact 181).pointIds 181), (.leaf 3 (Common.fact 182).pointIds 182), (.leaf 4 (Common.fact 183).pointIds 183), (.leaf 5 (Common.fact 184).pointIds 184), (.leaf 6 (Common.fact 561).pointIds 561)]
theorem treeEq0175 : B0175.tree = HexagonCover.NBand.M7700_7900.SplitData.node0175 := by
  change Tree.branch (113 : Fin 172) _ = Tree.branch (113 : Fin 172) _
  apply congrArg (Tree.branch (113 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0176
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0174 : Block := .branch 143 ![1267650600228229401496703205761, 302231526961251331606018, 77919046967349146032132, 5846006549323611672814816702117587414890911391752, 182688053115506591816447190585133387587640197136, 233840261972987002208454690542538204970878178295840, 27924422059968530543904637523678341890112] ![(.leaf 0 (Common.fact 229).pointIds 229), (.leaf 1 (Common.fact 230).pointIds 230), (.leaf 2 (Common.fact 231).pointIds 231), (.leaf 3 (Common.fact 232).pointIds 232), B0175, (.leaf 5 (Common.fact 234).pointIds 234), (.leaf 6 (Common.fact 560).pointIds 560)]
theorem treeEq0174 : B0174.tree = HexagonCover.NBand.M7700_7900.SplitData.node0174 := by
  change Tree.branch (143 : Fin 172) _ = Tree.branch (143 : Fin 172) _
  apply congrArg (Tree.branch (143 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0175
  · rfl
  · rfl

def B0173 : Block := .branch 129 ![1267650600228229401496703205761, 302231526961251331606018, 77919046967349146032132, 5846006549323611672894044864631851752484455342088, 185545336094068327906456454488816458905593937936, 233840261972987002208454690542538204970878178295840, 27243857326126653616977888308814805467200] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), (.leaf 4 (Common.fact 559).pointIds 559), (.leaf 5 (Common.fact 123).pointIds 123), B0174]
theorem treeEq0173 : B0173.tree = HexagonCover.NBand.M7700_7900.SplitData.node0173 := by
  change Tree.branch (129 : Fin 172) _ = Tree.branch (129 : Fin 172) _
  apply congrArg (Tree.branch (129 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0174

def B0172 : Block := .branch 130 ![1267650600228229401496703205761, 302231526961251331606018, 77919046967349146032132, 5846006549323611672894044864631851752484455342088, 185545336094068327906456454488816458905593937936, 233840261972987002208454690542538204970878178295840, 27243857326126653616977888308814805467200] ![(.leaf 0 (Common.fact 223).pointIds 223), (.leaf 1 (Common.fact 224).pointIds 224), (.leaf 2 (Common.fact 225).pointIds 225), (.leaf 3 (Common.fact 226).pointIds 226), (.leaf 4 (Common.fact 558).pointIds 558), (.leaf 5 (Common.fact 227).pointIds 227), B0173]
theorem treeEq0172 : B0172.tree = HexagonCover.NBand.M7700_7900.SplitData.node0172 := by
  change Tree.branch (130 : Fin 172) _ = Tree.branch (130 : Fin 172) _
  apply congrArg (Tree.branch (130 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0173

def B0171 : Block := .branch 131 ![1267650600228229401496703205761, 302231526961251331606018, 77919046967349146032132, 5846006549323611672894044864631851752484455342088, 185545336094068327906456454488816458905593937936, 233840261972987002208454690542538204970878178295840, 27243857326126653616977888308814805467200] ![(.leaf 0 (Common.fact 254).pointIds 254), (.leaf 1 (Common.fact 255).pointIds 255), (.leaf 2 (Common.fact 256).pointIds 256), (.leaf 3 (Common.fact 257).pointIds 257), (.leaf 4 (Common.fact 557).pointIds 557), (.leaf 5 (Common.fact 258).pointIds 258), B0172]
theorem treeEq0171 : B0171.tree = HexagonCover.NBand.M7700_7900.SplitData.node0171 := by
  change Tree.branch (131 : Fin 172) _ = Tree.branch (131 : Fin 172) _
  apply congrArg (Tree.branch (131 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0172

def B0170 : Block := .branch 162 ![1267650600228229401496703205761, 302231526961251331606018, 77919046967349146032132, 79305533766719673860725170184, 185545336094068327906456454488816458905593937936, 233840261972987002208454690542538204970878178295840, 27243857326443566267034945659188981268544] ![(.leaf 0 (Common.fact 375).pointIds 375), (.leaf 1 (Common.fact 376).pointIds 376), (.leaf 2 (Common.fact 377).pointIds 377), B0171, (.leaf 4 (Common.fact 556).pointIds 556), (.leaf 5 (Common.fact 378).pointIds 378), (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq0170 : B0170.tree = HexagonCover.NBand.M7700_7900.SplitData.node0170 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0171
  · rfl
  · rfl
  · rfl

def B0169 : Block := .branch 165 ![1267650600228229401496703205761, 302231526961251331606018, 77919046967349146032132, 79305533766719673860725170184, 185545336094068327906456454488816458905593937936, 187072209578398108825936775895617148341888336920608, 27243857326443566267034945659188981268544] ![(.leaf 0 (Common.fact 380).pointIds 380), (.leaf 1 (Common.fact 381).pointIds 381), (.leaf 2 (Common.fact 382).pointIds 382), (.leaf 3 (Common.fact 383).pointIds 383), (.leaf 4 (Common.fact 555).pointIds 555), B0170, (.leaf 0 [] 0)]
theorem treeEq0169 : B0169.tree = HexagonCover.NBand.M7700_7900.SplitData.node0169 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0170
  · rfl

def B0168 : Block := .branch 167 ![1267650600228229401496703205761, 302231526961251331606018, 77919046967349146032132, 79305533766719673860725170184, 185545336094068327906456454488816458905593937936, 42535295865117307932921825928971419680, 27243857326443566267034945659188981268544] ![(.leaf 0 (Common.fact 549).pointIds 549), (.leaf 1 (Common.fact 550).pointIds 550), (.leaf 2 (Common.fact 551).pointIds 551), (.leaf 3 (Common.fact 552).pointIds 552), (.leaf 4 (Common.fact 553).pointIds 553), B0169, (.leaf 6 (Common.fact 554).pointIds 554)]
theorem treeEq0168 : B0168.tree = HexagonCover.NBand.M7700_7900.SplitData.node0168 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0169
  · rfl

def B0167 : Block := .branch 151 ![1267650600228229401496703205761, 302231526961251331606018, 77919046967349146032132, 79305533766719673860725170184, 182690840708656408144339882549917468632828444688, 42535295865117307932921825928971419680, 27243857326443566267034945659188981268544] ![(.leaf 0 (Common.fact 241).pointIds 241), (.leaf 1 (Common.fact 242).pointIds 242), (.leaf 2 (Common.fact 243).pointIds 243), (.leaf 3 (Common.fact 244).pointIds 244), B0168, (.leaf 5 (Common.fact 496).pointIds 496), (.leaf 6 (Common.fact 548).pointIds 548)]
theorem treeEq0167 : B0167.tree = HexagonCover.NBand.M7700_7900.SplitData.node0167 := by
  change Tree.branch (151 : Fin 172) _ = Tree.branch (151 : Fin 172) _
  apply congrArg (Tree.branch (151 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0168
  · rfl
  · rfl

def B0137 : Block := .branch 108 ![1267650600228229401496703205761, 302231526961251331606018, 77937529740219874547716, 79344219392947341994315767816, 182869246670244653129472168296098655524876288016, 42535295865117307932921825928971419680, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 279).pointIds 279), (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 281).pointIds 281), (.leaf 3 (Common.fact 282).pointIds 282), Tip0135_0138, (.leaf 5 (Common.fact 283).pointIds 283), B0167]
theorem treeEq0137 : B0137.tree = HexagonCover.NBand.M7700_7900.SplitData.node0137 := by
  change Tree.branch (108 : Fin 172) _ = Tree.branch (108 : Fin 172) _
  apply congrArg (Tree.branch (108 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0167

def B0180 : Block := .branch 142 ![385, 1538, 6148, 24584, 182690492259512843362630125267682850080190201872, 393248, 11692013125891080347554491270338483033280421036096] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), (.leaf 4 (Common.fact 571).pointIds 571), (.leaf 5 (Common.fact 116).pointIds 116), (.leaf 6 (Common.fact 572).pointIds 572)]
theorem treeEq0180 : B0180.tree = HexagonCover.NBand.M7700_7900.SplitData.node0180 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0179 : Block := .branch 163 ![385, 1538, 6148, 24584, 182690492259512843362630125267682850080190201872, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 287).pointIds 287), (.leaf 1 (Common.fact 288).pointIds 288), (.leaf 2 (Common.fact 289).pointIds 289), (.leaf 3 (Common.fact 290).pointIds 290), (.leaf 4 (Common.fact 570).pointIds 570), (.leaf 5 (Common.fact 291).pointIds 291), B0180]
theorem treeEq0179 : B0179.tree = HexagonCover.NBand.M7700_7900.SplitData.node0179 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0180

def B0178 : Block := .branch 165 ![385, 1538, 6148, 24584, 182690492259512843362630125267682850080190201872, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 380).pointIds 380), (.leaf 1 (Common.fact 381).pointIds 381), (.leaf 2 (Common.fact 382).pointIds 382), (.leaf 3 (Common.fact 383).pointIds 383), (.leaf 4 (Common.fact 569).pointIds 569), B0179, (.leaf 0 [] 0)]
theorem treeEq0178 : B0178.tree = HexagonCover.NBand.M7700_7900.SplitData.node0178 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0179
  · rfl

def B0177 : Block := .branch 167 ![385, 1538, 6148, 24584, 182690492259512843362630125267682850080190201872, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 549).pointIds 549), (.leaf 1 (Common.fact 550).pointIds 550), (.leaf 2 (Common.fact 551).pointIds 551), (.leaf 3 (Common.fact 552).pointIds 552), (.leaf 4 (Common.fact 568).pointIds 568), B0178, (.leaf 6 (Common.fact 554).pointIds 554)]
theorem treeEq0177 : B0177.tree = HexagonCover.NBand.M7700_7900.SplitData.node0177 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0178
  · rfl

def B0136 : Block := .branch 107 ![1267650600228229401496703205761, 302231526961251331606018, 77937529740219874547716, 79344219392947341994315767816, 182869246670244653129472168296098655524876288016, 42535295865117307932921825928971419680, 27249173913908152272099834104274082070592] ![(.leaf 0 (Common.fact 310).pointIds 310), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), B0137, B0177, (.leaf 5 (Common.fact 314).pointIds 314), (.leaf 6 (Common.fact 494).pointIds 494)]
theorem treeEq0136 : B0136.tree = HexagonCover.NBand.M7700_7900.SplitData.node0136 := by
  change Tree.branch (107 : Fin 172) _ = Tree.branch (107 : Fin 172) _
  apply congrArg (Tree.branch (107 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0137
  · exact treeEq0177
  · rfl
  · rfl

def B0181 : Block := .branch 170 ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 77919046967349146032132, 158533696280984011454269120520, 182690840708656408144339882549917468632828444688, 42535295865117307932921825928971419680, 27243857003192663208836448277529663897664] ![(.leaf 0 (Common.fact 573).pointIds 573), (.leaf 1 (Common.fact 563).pointIds 563), (.leaf 2 (Common.fact 533).pointIds 533), (.leaf 3 (Common.fact 574).pointIds 574), (.leaf 4 (Common.fact 575).pointIds 575), (.leaf 5 (Common.fact 525).pointIds 525), (.leaf 6 (Common.fact 576).pointIds 576)]
theorem treeEq0181 : B0181.tree = HexagonCover.NBand.M7700_7900.SplitData.node0181 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0135 : Block := .branch 100 ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 77937529740219874547716, 237800544421476017181403668488, 182869246670244653129472168296098655524876288016, 42535295865117307932921825928971419680, 27249173913908152272099834104274082070592] ![B0136, (.leaf 1 (Common.fact 489).pointIds 489), (.leaf 2 (Common.fact 490).pointIds 490), (.leaf 3 (Common.fact 491).pointIds 491), (.leaf 4 (Common.fact 492).pointIds 492), (.leaf 5 (Common.fact 493).pointIds 493), B0181]
theorem treeEq0135 : B0135.tree = HexagonCover.NBand.M7700_7900.SplitData.node0135 := by
  change Tree.branch (100 : Fin 172) _ = Tree.branch (100 : Fin 172) _
  apply congrArg (Tree.branch (100 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0136
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0181

theorem accepted0135 : B0135.accepted = true := by decide +kernel
theorem checked0135 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7700_7900.SplitData.node0135 (maskNeeds ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 77937529740219874547716, 237800544421476017181403668488, 182869246670244653129472168296098655524876288016, 42535295865117307932921825928971419680, 27249173913908152272099834104274082070592]) := by
  rw [← treeEq0135]
  exact B0135.sound accepted0135
#print axioms checked0135

def Tip0130_0135 : Block := .tip HexagonCover.NBand.M7700_7900.SplitData.node0135 ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 77937529740219874547716, 237800544421476017181403668488, 182869246670244653129472168296098655524876288016, 42535295865117307932921825928971419680, 27249173913908152272099834104274082070592] checked0135
def B0185 : Block := .branch 142 ![385, 1538, 6148, 24584, 182687704666362864933916929118064052644079566864, 393248, 11692013125891080347554491270338483033280421036096] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), (.leaf 4 (Common.fact 580).pointIds 580), (.leaf 5 (Common.fact 116).pointIds 116), (.leaf 6 (Common.fact 572).pointIds 572)]
theorem treeEq0185 : B0185.tree = HexagonCover.NBand.M7700_7900.SplitData.node0185 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0184 : Block := .branch 163 ![385, 1538, 6148, 24584, 182687704666362864933916929118064052644079566864, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 287).pointIds 287), (.leaf 1 (Common.fact 288).pointIds 288), (.leaf 2 (Common.fact 289).pointIds 289), (.leaf 3 (Common.fact 290).pointIds 290), (.leaf 4 (Common.fact 579).pointIds 579), (.leaf 5 (Common.fact 291).pointIds 291), B0185]
theorem treeEq0184 : B0184.tree = HexagonCover.NBand.M7700_7900.SplitData.node0184 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0185

def B0183 : Block := .branch 165 ![385, 1538, 6148, 24584, 182687704666362864933916929118064052644079566864, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 380).pointIds 380), (.leaf 1 (Common.fact 381).pointIds 381), (.leaf 2 (Common.fact 382).pointIds 382), (.leaf 3 (Common.fact 383).pointIds 383), (.leaf 4 (Common.fact 578).pointIds 578), B0184, (.leaf 0 [] 0)]
theorem treeEq0183 : B0183.tree = HexagonCover.NBand.M7700_7900.SplitData.node0183 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0184
  · rfl

def B0182 : Block := .branch 167 ![385, 1538, 6148, 24584, 182687704666362864933916929118064052644079566864, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 549).pointIds 549), (.leaf 1 (Common.fact 550).pointIds 550), (.leaf 2 (Common.fact 551).pointIds 551), (.leaf 3 (Common.fact 552).pointIds 552), (.leaf 4 (Common.fact 577).pointIds 577), B0183, (.leaf 6 (Common.fact 554).pointIds 554)]
theorem treeEq0182 : B0182.tree = HexagonCover.NBand.M7700_7900.SplitData.node0182 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0183
  · rfl

def B0134 : Block := .branch 97 ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 77946771197023982983172, 79344219392947341994315767816, 182869246670244653129472168296098655524876288016, 42535295865117307932921825928971419680, 38138209655378183102927821542090664837184] ![(.leaf 0 (Common.fact 316).pointIds 316), (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), Tip0130_0135, B0182, (.leaf 5 (Common.fact 320).pointIds 320), (.leaf 6 (Common.fact 488).pointIds 488)]
theorem treeEq0134 : B0134.tree = HexagonCover.NBand.M7700_7900.SplitData.node0134 := by
  change Tree.branch (97 : Fin 172) _ = Tree.branch (97 : Fin 172) _
  apply congrArg (Tree.branch (97 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0182
  · rfl
  · rfl

def B0196 : Block := .branch 170 ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 77919046967349146032132, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 42535295865117307932921825928971419680, 2854517184751050635123743823611460756077805632] ![(.leaf 0 (Common.fact 573).pointIds 573), (.leaf 1 (Common.fact 563).pointIds 563), (.leaf 2 (Common.fact 533).pointIds 533), (.leaf 3 (Common.fact 593).pointIds 593), (.leaf 4 (Common.fact 529).pointIds 529), (.leaf 5 (Common.fact 525).pointIds 525), (.leaf 6 (Common.fact 594).pointIds 594)]
theorem treeEq0196 : B0196.tree = HexagonCover.NBand.M7700_7900.SplitData.node0196 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0195 : Block := .branch 108 ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 77919046967349146032132, 174224571863678988303902555348386002788360, 11874700803313586210404939265819799534704452010000, 42535295865117307932921825928971419680, 2854522629268921370139159237605179664369188928] ![(.leaf 0 (Common.fact 279).pointIds 279), (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 281).pointIds 281), (.leaf 3 (Common.fact 282).pointIds 282), B0196, (.leaf 5 (Common.fact 283).pointIds 283), (.leaf 6 (Common.fact 592).pointIds 592)]
theorem treeEq0195 : B0195.tree = HexagonCover.NBand.M7700_7900.SplitData.node0195 := by
  change Tree.branch (108 : Fin 172) _ = Tree.branch (108 : Fin 172) _
  apply congrArg (Tree.branch (108 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0196
  · rfl
  · rfl

def B0194 : Block := .branch 119 ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 77919046967349146032132, 174224571863678988303902555348386002788360, 11874700803313586210404939265819799534704452010000, 42535295865117307932921825928971419680, 2854522629268921370139159237605179664369188928] ![(.leaf 0 (Common.fact 273).pointIds 273), (.leaf 1 (Common.fact 274).pointIds 274), (.leaf 2 (Common.fact 275).pointIds 275), (.leaf 3 (Common.fact 276).pointIds 276), B0195, (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 591).pointIds 591)]
theorem treeEq0194 : B0194.tree = HexagonCover.NBand.M7700_7900.SplitData.node0194 := by
  change Tree.branch (119 : Fin 172) _ = Tree.branch (119 : Fin 172) _
  apply congrArg (Tree.branch (119 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0195
  · rfl
  · rfl

def B0193 : Block := .branch 129 ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 77919046967349146032132, 174224571863758216466416819685979546738696, 11874700803313586210404939265819799534704452010000, 42535295865117307932921825928971419680, 2854522629268921370139159237605179664369188928] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B0194, (.leaf 5 (Common.fact 123).pointIds 123), (.leaf 6 (Common.fact 590).pointIds 590)]
theorem treeEq0193 : B0193.tree = HexagonCover.NBand.M7700_7900.SplitData.node0193 := by
  change Tree.branch (129 : Fin 172) _ = Tree.branch (129 : Fin 172) _
  apply congrArg (Tree.branch (129 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0194
  · rfl
  · rfl

def B0192 : Block := .branch 97 ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 77928288424153254467588, 174224571863599760141388291010792458838024, 11874701151762729937445925852315397544835100540944, 42535295865117307932921825928971419680, 2854533518304663157237382627560640389490147392] ![(.leaf 0 (Common.fact 316).pointIds 316), (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), B0193, (.leaf 4 (Common.fact 589).pointIds 589), (.leaf 5 (Common.fact 320).pointIds 320), (.leaf 6 (Common.fact 488).pointIds 488)]
theorem treeEq0192 : B0192.tree = HexagonCover.NBand.M7700_7900.SplitData.node0192 := by
  change Tree.branch (97 : Fin 172) _ = Tree.branch (97 : Fin 172) _
  apply congrArg (Tree.branch (97 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0193
  · rfl
  · rfl
  · rfl

def B0191 : Block := .branch 107 ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 77928288424153254467588, 174224571863599760141388291010792458838024, 11874701151762729937445925852315397544835100540944, 42535295865117307932921825928971419680, 2854533523621575140377046119175868630611525696] ![(.leaf 0 (Common.fact 310).pointIds 310), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), B0192, (.leaf 4 (Common.fact 588).pointIds 588), (.leaf 5 (Common.fact 314).pointIds 314), (.leaf 6 (Common.fact 494).pointIds 494)]
theorem treeEq0191 : B0191.tree = HexagonCover.NBand.M7700_7900.SplitData.node0191 := by
  change Tree.branch (107 : Fin 172) _ = Tree.branch (107 : Fin 172) _
  apply congrArg (Tree.branch (107 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0192
  · rfl
  · rfl
  · rfl

def B0190 : Block := .branch 118 ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 77928288424153254467588, 174224571863599760141388291010792458838024, 11874701151762729937445925852315397544835100540944, 42535295865117307932921825928971419680, 2854533523621575140377046119175868630611525696] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), B0191, (.leaf 4 (Common.fact 586).pointIds 586), (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 587).pointIds 587)]
theorem treeEq0190 : B0190.tree = HexagonCover.NBand.M7700_7900.SplitData.node0190 := by
  change Tree.branch (118 : Fin 172) _ = Tree.branch (118 : Fin 172) _
  apply congrArg (Tree.branch (118 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0191
  · rfl
  · rfl
  · rfl

def B0189 : Block := .branch 128 ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 77928288424153254467588, 174224571863599760141388291010792458838024, 11874701151762729937445925852315397544835100540944, 42535295865117307932921825928971419680, 2854533523621575140377046119175868630611525696] ![(.leaf 0 (Common.fact 298).pointIds 298), (.leaf 1 (Common.fact 299).pointIds 299), (.leaf 2 (Common.fact 300).pointIds 300), B0190, (.leaf 4 (Common.fact 584).pointIds 584), (.leaf 5 (Common.fact 302).pointIds 302), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq0189 : B0189.tree = HexagonCover.NBand.M7700_7900.SplitData.node0189 := by
  change Tree.branch (128 : Fin 172) _ = Tree.branch (128 : Fin 172) _
  apply congrArg (Tree.branch (128 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0190
  · rfl
  · rfl
  · rfl

def B0188 : Block := .branch 137 ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 77928288424153254467588, 79266848140492005727134572552, 11874701151762729937445925852315397544835100540944, 42535295865117307932921825928971419680, 2854533523621575140377046119175868630611525696] ![(.leaf 0 (Common.fact 293).pointIds 293), (.leaf 1 (Common.fact 294).pointIds 294), (.leaf 2 (Common.fact 295).pointIds 295), B0189, (.leaf 4 (Common.fact 583).pointIds 583), (.leaf 5 (Common.fact 297).pointIds 297), (.leaf 0 [] 0)]
theorem treeEq0188 : B0188.tree = HexagonCover.NBand.M7700_7900.SplitData.node0188 := by
  change Tree.branch (137 : Fin 172) _ = Tree.branch (137 : Fin 172) _
  apply congrArg (Tree.branch (137 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0189
  · rfl
  · rfl
  · rfl

def B0187 : Block := .branch 151 ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 77928288424153254467588, 79266848140492005727134572552, 11874701151762729937445925852315397544835100540944, 42535295865117307932921825928971419680, 38138209655378260474180276878357846032448] ![(.leaf 0 (Common.fact 241).pointIds 241), (.leaf 1 (Common.fact 242).pointIds 242), (.leaf 2 (Common.fact 243).pointIds 243), (.leaf 3 (Common.fact 244).pointIds 244), (.leaf 4 (Common.fact 582).pointIds 582), (.leaf 5 (Common.fact 496).pointIds 496), B0188]
theorem treeEq0187 : B0187.tree = HexagonCover.NBand.M7700_7900.SplitData.node0187 := by
  change Tree.branch (151 : Fin 172) _ = Tree.branch (151 : Fin 172) _
  apply congrArg (Tree.branch (151 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0188

def B0186 : Block := .branch 163 ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 77928288424153254467588, 79266848140492005727134572552, 182688053115506591816447190585133387587640197136, 42535295865117307932921825928971419680, 38138209655378260474180276878357846032448] ![(.leaf 0 (Common.fact 287).pointIds 287), (.leaf 1 (Common.fact 288).pointIds 288), (.leaf 2 (Common.fact 289).pointIds 289), (.leaf 3 (Common.fact 290).pointIds 290), B0187, (.leaf 5 (Common.fact 291).pointIds 291), (.leaf 6 (Common.fact 581).pointIds 581)]
theorem treeEq0186 : B0186.tree = HexagonCover.NBand.M7700_7900.SplitData.node0186 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0187
  · rfl
  · rfl

def B0133 : Block := .branch 86 ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 77946771197023982983172, 79266848140492005727134572552, 182869246670244653129472168296098655524876288016, 42535295865117307932921825928971419680, 38138209655378183102927821542090664837184] ![(.leaf 0 (Common.fact 360).pointIds 360), (.leaf 1 (Common.fact 361).pointIds 361), (.leaf 2 (Common.fact 362).pointIds 362), B0134, (.leaf 4 (Common.fact 363).pointIds 363), (.leaf 5 (Common.fact 364).pointIds 364), B0186]
theorem treeEq0133 : B0133.tree = HexagonCover.NBand.M7700_7900.SplitData.node0133 := by
  change Tree.branch (86 : Fin 172) _ = Tree.branch (86 : Fin 172) _
  apply congrArg (Tree.branch (86 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0134
  · rfl
  · rfl
  · exact treeEq0186

def B0132 : Block := .branch 169 ![604462909807314587353473, 302232391652379786741250, 77946771197023982983172, 79266848140492005727134572552, 182869246670244653129472168296098655524876288016, 42535295865117307932921825928971419680, 38138209655378183102927821542090664837184] ![B0133, (.leaf 1 (Common.fact 482).pointIds 482), (.leaf 2 (Common.fact 483).pointIds 483), (.leaf 3 (Common.fact 484).pointIds 484), (.leaf 4 (Common.fact 485).pointIds 485), (.leaf 5 (Common.fact 486).pointIds 486), (.leaf 6 (Common.fact 487).pointIds 487)]
theorem treeEq0132 : B0132.tree = HexagonCover.NBand.M7700_7900.SplitData.node0132 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0133
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0131 : Block := .branch 132 ![604462909807314587353473, 302232391652379786741250, 77946771197023982983172, 79266848140492005727134572552, 182869246670244653129472168296098655524876288016, 42535295865117307932921825928971419680, 32693691784643167687513827823182373453888] ![(.leaf 0 (Common.fact 202).pointIds 202), (.leaf 1 (Common.fact 203).pointIds 203), (.leaf 2 (Common.fact 204).pointIds 204), (.leaf 3 (Common.fact 205).pointIds 205), (.leaf 4 (Common.fact 481).pointIds 481), (.leaf 5 (Common.fact 207).pointIds 207), B0132]
theorem treeEq0131 : B0131.tree = HexagonCover.NBand.M7700_7900.SplitData.node0131 := by
  change Tree.branch (132 : Fin 172) _ = Tree.branch (132 : Fin 172) _
  apply congrArg (Tree.branch (132 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0132

def B0130 : Block := .branch 133 ![604462909807314587353473, 302232391652379786741250, 77946771197023982983172, 79266848140492005727134572552, 182869246670244653129472168296098655524876288016, 42535295865117307932921825928971419680, 21804656043173136856685840385365790687296] ![(.leaf 0 (Common.fact 161).pointIds 161), (.leaf 1 (Common.fact 162).pointIds 162), (.leaf 2 (Common.fact 163).pointIds 163), (.leaf 3 (Common.fact 164).pointIds 164), (.leaf 4 (Common.fact 480).pointIds 480), (.leaf 5 (Common.fact 166).pointIds 166), B0131]
theorem treeEq0130 : B0130.tree = HexagonCover.NBand.M7700_7900.SplitData.node0130 := by
  change Tree.branch (133 : Fin 172) _ = Tree.branch (133 : Fin 172) _
  apply congrArg (Tree.branch (133 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0131

theorem accepted0130 : B0130.accepted = true := by decide +kernel
theorem checked0130 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7700_7900.SplitData.node0130 (maskNeeds ![604462909807314587353473, 302232391652379786741250, 77946771197023982983172, 79266848140492005727134572552, 182869246670244653129472168296098655524876288016, 42535295865117307932921825928971419680, 21804656043173136856685840385365790687296]) := by
  rw [← treeEq0130]
  exact B0130.sound accepted0130
#print axioms checked0130

def B0225 : Block := .branch 170 ![748288838313422304507415653225311531735138114208129, 302231526961251331606018, 40177008592539403425796, 5846006549323611672814816702117587414890911391752, 182699203488105857128017958444269711768393187344, 233840261972987002208454690542538204970878178295840, 22479903864714497318107048729925266178112] ![(.leaf 0 (Common.fact 634).pointIds 634), (.leaf 1 (Common.fact 563).pointIds 563), (.leaf 2 (Common.fact 635).pointIds 635), (.leaf 3 (Common.fact 564).pointIds 564), (.leaf 4 (Common.fact 565).pointIds 565), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 636).pointIds 636)]
theorem treeEq0225 : B0225.tree = HexagonCover.NBand.M7700_7900.SplitData.node0225 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0224 : Block := .branch 129 ![748288838313422304507415653225311531735138114208129, 302231526961251331606018, 40177008592539403425796, 5846006549323611672894044864631851752484455342088, 185553698873517776890134530383168702041158680592, 233840261972987002208454690542538204970878178295840, 21799339130872620391180299515061729755200] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), (.leaf 4 (Common.fact 633).pointIds 633), (.leaf 5 (Common.fact 123).pointIds 123), B0225]
theorem treeEq0224 : B0224.tree = HexagonCover.NBand.M7700_7900.SplitData.node0224 := by
  change Tree.branch (129 : Fin 172) _ = Tree.branch (129 : Fin 172) _
  apply congrArg (Tree.branch (129 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0225

def B0223 : Block := .branch 130 ![748288838313422304507415653225311531735138114208129, 302231526961251331606018, 40177008592539403425796, 5846006549323611672894044864631851752484455342088, 185553698873517776890134530383168702041158680592, 233840261972987002208454690542538204970878178295840, 21799339130872620391180299515061729755200] ![(.leaf 0 (Common.fact 223).pointIds 223), (.leaf 1 (Common.fact 224).pointIds 224), (.leaf 2 (Common.fact 225).pointIds 225), (.leaf 3 (Common.fact 226).pointIds 226), (.leaf 4 (Common.fact 632).pointIds 632), (.leaf 5 (Common.fact 227).pointIds 227), B0224]
theorem treeEq0223 : B0223.tree = HexagonCover.NBand.M7700_7900.SplitData.node0223 := by
  change Tree.branch (130 : Fin 172) _ = Tree.branch (130 : Fin 172) _
  apply congrArg (Tree.branch (130 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0224

def B0222 : Block := .branch 131 ![748288838313422304507415653225311531735138114208129, 302231526961251331606018, 40177008592539403425796, 5846006549323611672894044864631851752484455342088, 185553698873517776890134530383168702041158680592, 233840261972987002208454690542538204970878178295840, 21799339130872620391180299515061729755200] ![(.leaf 0 (Common.fact 254).pointIds 254), (.leaf 1 (Common.fact 255).pointIds 255), (.leaf 2 (Common.fact 256).pointIds 256), (.leaf 3 (Common.fact 257).pointIds 257), (.leaf 4 (Common.fact 631).pointIds 631), (.leaf 5 (Common.fact 258).pointIds 258), B0223]
theorem treeEq0222 : B0222.tree = HexagonCover.NBand.M7700_7900.SplitData.node0222 := by
  change Tree.branch (131 : Fin 172) _ = Tree.branch (131 : Fin 172) _
  apply congrArg (Tree.branch (131 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0223

def B0221 : Block := .branch 132 ![748288838313422304507415653225311531735138114208129, 302231526961251331606018, 40177008592539403425796, 5846006549323611672894044864631851752484455342088, 185553698873517776890134530383168702041158680592, 233840261972987002208454690542538204970878178295840, 21799339130872620391180299515061729755200] ![(.leaf 0 (Common.fact 202).pointIds 202), (.leaf 1 (Common.fact 203).pointIds 203), (.leaf 2 (Common.fact 204).pointIds 204), (.leaf 3 (Common.fact 205).pointIds 205), (.leaf 4 (Common.fact 630).pointIds 630), (.leaf 5 (Common.fact 207).pointIds 207), B0222]
theorem treeEq0221 : B0221.tree = HexagonCover.NBand.M7700_7900.SplitData.node0221 := by
  change Tree.branch (132 : Fin 172) _ = Tree.branch (132 : Fin 172) _
  apply congrArg (Tree.branch (132 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0222

def B0220 : Block := .branch 133 ![748288838313422304507415653225311531735138114208129, 302231526961251331606018, 40177008592539403425796, 5846006549323611672894044864631851752484455342088, 185553698873517776890134530383168702041158680592, 233840261972987002208454690542538204970878178295840, 21799339130872620391180299515061729755200] ![(.leaf 0 (Common.fact 161).pointIds 161), (.leaf 1 (Common.fact 162).pointIds 162), (.leaf 2 (Common.fact 163).pointIds 163), (.leaf 3 (Common.fact 164).pointIds 164), (.leaf 4 (Common.fact 629).pointIds 629), (.leaf 5 (Common.fact 166).pointIds 166), B0221]
theorem treeEq0220 : B0220.tree = HexagonCover.NBand.M7700_7900.SplitData.node0220 := by
  change Tree.branch (133 : Fin 172) _ = Tree.branch (133 : Fin 172) _
  apply congrArg (Tree.branch (133 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0221

def B0219 : Block := .branch 79 ![748288838313422304507415652620848621927823526855041, 302231671076439407461890, 40177008592539403425796, 5846006549323611672894044864631851752484455342088, 185553698873517776890134530383168702041158680592, 233840261972987002208454690542538204970878178295840, 11692013120446562476819011702967621022683365900352] ![B0220, (.leaf 1 (Common.fact 209).pointIds 209), (.leaf 2 (Common.fact 210).pointIds 210), (.leaf 3 (Common.fact 211).pointIds 211), (.leaf 4 (Common.fact 212).pointIds 212), (.leaf 5 (Common.fact 213).pointIds 213), (.leaf 6 (Common.fact 628).pointIds 628)]
theorem treeEq0219 : B0219.tree = HexagonCover.NBand.M7700_7900.SplitData.node0219 := by
  change Tree.branch (79 : Fin 172) _ = Tree.branch (79 : Fin 172) _
  apply congrArg (Tree.branch (79 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0220
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0218 : Block := .branch 86 ![748288838313422304507415652620848621927823526855041, 302231671076439407461890, 40186267993373277165572, 5846006549323611672893967493379396416217274146824, 185553698873517776890134530383168702041158680592, 233840261972987002208454690542538204970878178295840, 11692013120446562476819011702967621022683365900352] ![(.leaf 0 (Common.fact 360).pointIds 360), (.leaf 1 (Common.fact 361).pointIds 361), (.leaf 2 (Common.fact 362).pointIds 362), B0219, (.leaf 4 (Common.fact 363).pointIds 363), (.leaf 5 (Common.fact 364).pointIds 364), (.leaf 6 (Common.fact 627).pointIds 627)]
theorem treeEq0218 : B0218.tree = HexagonCover.NBand.M7700_7900.SplitData.node0218 := by
  change Tree.branch (86 : Fin 172) _ = Tree.branch (86 : Fin 172) _
  apply congrArg (Tree.branch (86 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0219
  · rfl
  · rfl
  · rfl

def B0217 : Block := .branch 138 ![748288838313422304507415652620848621927823526855041, 302231671076439407461890, 40186267993373277165572, 5846006549323611672893967493379396416217274146824, 185553350424374049849147943887570691910510149648, 233840261972987002208454690542538204970878178295840, 11692013120446562476819011702967621022683365900352] ![(.leaf 0 (Common.fact 155).pointIds 155), (.leaf 1 (Common.fact 156).pointIds 156), (.leaf 2 (Common.fact 157).pointIds 157), (.leaf 3 (Common.fact 158).pointIds 158), B0218, (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 626).pointIds 626)]
theorem treeEq0217 : B0217.tree = HexagonCover.NBand.M7700_7900.SplitData.node0217 := by
  change Tree.branch (138 : Fin 172) _ = Tree.branch (138 : Fin 172) _
  apply congrArg (Tree.branch (138 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0218
  · rfl
  · rfl

def B0216 : Block := .branch 140 ![748288838313422304507415652620848621927823526855041, 302231671076439407461890, 40186267993373277165572, 5846006549323611672893967493379396416217274146824, 185553350424374049849147943887570691910510149648, 233840261972987002208454690542538204970878178295840, 11692013120446562476819011702967621022683365900352] ![(.leaf 0 (Common.fact 185).pointIds 185), (.leaf 1 (Common.fact 186).pointIds 186), (.leaf 2 (Common.fact 187).pointIds 187), (.leaf 3 (Common.fact 188).pointIds 188), B0217, (.leaf 5 (Common.fact 189).pointIds 189), (.leaf 6 (Common.fact 625).pointIds 625)]
theorem treeEq0216 : B0216.tree = HexagonCover.NBand.M7700_7900.SplitData.node0216 := by
  change Tree.branch (140 : Fin 172) _ = Tree.branch (140 : Fin 172) _
  apply congrArg (Tree.branch (140 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0217
  · rfl
  · rfl

def B0215 : Block := .branch 141 ![748288838313422304507415652620848621927823526855041, 302231671076439407461890, 40186267993373277165572, 5846006549323611672893967493379396416217274146824, 185553350424374049849147943887570691910510149648, 233840261972987002208454690542538204970878178295840, 11692013120446562476819011702967621022683365900352] ![(.leaf 0 (Common.fact 248).pointIds 248), (.leaf 1 (Common.fact 249).pointIds 249), (.leaf 2 (Common.fact 250).pointIds 250), (.leaf 3 (Common.fact 251).pointIds 251), B0216, (.leaf 5 (Common.fact 252).pointIds 252), (.leaf 6 (Common.fact 624).pointIds 624)]
theorem treeEq0215 : B0215.tree = HexagonCover.NBand.M7700_7900.SplitData.node0215 := by
  change Tree.branch (141 : Fin 172) _ = Tree.branch (141 : Fin 172) _
  apply congrArg (Tree.branch (141 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0216
  · rfl
  · rfl

def B0214 : Block := .branch 142 ![748288838313422304507415652620848621927823526855041, 302231671076439407461890, 40186267993373277165572, 5846006549323611672893967493379396416217274146824, 185553350424374049849147943887570691910510149648, 233840261972987002208454690542538204970878178295840, 11692013120446562476819011702967621022683365900352] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), B0215, (.leaf 5 (Common.fact 116).pointIds 116), (.leaf 6 (Common.fact 623).pointIds 623)]
theorem treeEq0214 : B0214.tree = HexagonCover.NBand.M7700_7900.SplitData.node0214 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0215
  · rfl
  · rfl

def B0213 : Block := .branch 165 ![748288838313422304507415652620848621927823526855041, 302231671076439407461890, 40186267993373277165572, 5846006549323611672893967493379396416217274146824, 185553350424374049849147943887570691910510149648, 187072209578398108825936775895617148341888336920608, 11692013120446562476819011702967621022683365900352] ![(.leaf 0 (Common.fact 380).pointIds 380), (.leaf 1 (Common.fact 381).pointIds 381), (.leaf 2 (Common.fact 382).pointIds 382), (.leaf 3 (Common.fact 383).pointIds 383), (.leaf 4 (Common.fact 622).pointIds 622), B0214, (.leaf 0 [] 0)]
theorem treeEq0213 : B0213.tree = HexagonCover.NBand.M7700_7900.SplitData.node0213 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0214
  · rfl

def B0212 : Block := .branch 167 ![748288838313422304507415652620848621927823526855041, 302231671076439407461890, 40186267993373277165572, 5846006549323611672893967493379396416217274146824, 185553350424374049849147943887570691910510149648, 42535295865117307932921825928971419680, 11692013120446562476819011702967621022683365900352] ![(.leaf 0 (Common.fact 549).pointIds 549), (.leaf 1 (Common.fact 550).pointIds 550), (.leaf 2 (Common.fact 551).pointIds 551), (.leaf 3 (Common.fact 552).pointIds 552), (.leaf 4 (Common.fact 621).pointIds 621), B0213, (.leaf 6 (Common.fact 554).pointIds 554)]
theorem treeEq0212 : B0212.tree = HexagonCover.NBand.M7700_7900.SplitData.node0212 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0213
  · rfl

def B0211 : Block := .branch 143 ![748288838313422304507415652620848621927823526855041, 302231671076439407461890, 40186267993373277165572, 5846006549323611672893967493379396416217274146824, 185542200051774784537577176028434367729757159440, 42535295865117307932921825928971419680, 11692013120446562476819011702967621022683365900352] ![(.leaf 0 (Common.fact 229).pointIds 229), (.leaf 1 (Common.fact 230).pointIds 230), (.leaf 2 (Common.fact 231).pointIds 231), (.leaf 3 (Common.fact 232).pointIds 232), B0212, (.leaf 5 (Common.fact 234).pointIds 234), (.leaf 6 (Common.fact 620).pointIds 620)]
theorem treeEq0211 : B0211.tree = HexagonCover.NBand.M7700_7900.SplitData.node0211 := by
  change Tree.branch (143 : Fin 172) _ = Tree.branch (143 : Fin 172) _
  apply congrArg (Tree.branch (143 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0212
  · rfl
  · rfl

def B0210 : Block := .branch 75 ![748288838313422304507415652620848621927823526855041, 302231671076439407461890, 2407336130416115456004, 5846006549323611672894006179005624084350864744456, 185542200051774784537577176028434367729757159440, 42535295865117307932921825928971419680, 11692013120446562476819011702967621022683365900352] ![(.leaf 0 (Common.fact 424).pointIds 424), (.leaf 1 (Common.fact 425).pointIds 425), B0211, (.leaf 3 (Common.fact 618).pointIds 618), (.leaf 4 (Common.fact 427).pointIds 427), (.leaf 5 (Common.fact 428).pointIds 428), (.leaf 6 (Common.fact 619).pointIds 619)]
theorem treeEq0210 : B0210.tree = HexagonCover.NBand.M7700_7900.SplitData.node0210 := by
  change Tree.branch (75 : Fin 172) _ = Tree.branch (75 : Fin 172) _
  apply congrArg (Tree.branch (75 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0211
  · rfl
  · rfl
  · rfl
  · rfl

def B0209 : Block := .branch 162 ![748288838313422304507415652620848621927823526855041, 302231671076439407461890, 2407336130416115456004, 79266848140492005727134572552, 185542200051774784537577176028434367729757159440, 42535295865117307932921825928971419680, 11692013120446562476819011702967621022683365900352] ![(.leaf 0 (Common.fact 375).pointIds 375), (.leaf 1 (Common.fact 376).pointIds 376), (.leaf 2 (Common.fact 377).pointIds 377), B0210, (.leaf 4 (Common.fact 616).pointIds 616), (.leaf 5 (Common.fact 378).pointIds 378), (.leaf 6 (Common.fact 617).pointIds 617)]
theorem treeEq0209 : B0209.tree = HexagonCover.NBand.M7700_7900.SplitData.node0209 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0210
  · rfl
  · rfl
  · rfl

def B0208 : Block := .branch 124 ![748288838313422304507415652620848621927823526855041, 302231671076439407461890, 2407336130416115456004, 79266848140492005727134572552, 185542200051774784537577176028434367729757159440, 42535295865117307932921825928971419680, 11692013120425294828886453049001160109718880387136] ![(.leaf 0 (Common.fact 615).pointIds 615), (.leaf 1 (Common.fact 150).pointIds 150), (.leaf 2 (Common.fact 151).pointIds 151), (.leaf 3 (Common.fact 152).pointIds 152), (.leaf 4 (Common.fact 153).pointIds 153), (.leaf 5 (Common.fact 154).pointIds 154), B0209]
theorem treeEq0208 : B0208.tree = HexagonCover.NBand.M7700_7900.SplitData.node0208 := by
  change Tree.branch (124 : Fin 172) _ = Tree.branch (124 : Fin 172) _
  apply congrArg (Tree.branch (124 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0209

def B0207 : Block := .branch 169 ![10387129018270111715863986064851329, 302232535767567862597122, 2425782874489825007620, 79266848140492005727134572552, 185720606013363029522709461774615554621805002768, 42535295865117307932921825928971419680, 11692013120425294828886453049001160109718880387136] ![B0208, (.leaf 1 (Common.fact 482).pointIds 482), (.leaf 2 (Common.fact 483).pointIds 483), (.leaf 3 (Common.fact 484).pointIds 484), (.leaf 4 (Common.fact 485).pointIds 485), (.leaf 5 (Common.fact 486).pointIds 486), (.leaf 6 (Common.fact 614).pointIds 614)]
theorem treeEq0207 : B0207.tree = HexagonCover.NBand.M7700_7900.SplitData.node0207 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0208
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0206 : Block := .branch 163 ![10387129018270111715863986064851329, 302232535767567862597122, 2425782874489825007620, 79266848140492005727134572552, 185720606013363029522709461774615554621805002768, 42535295865117307932921825928971419680, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 287).pointIds 287), (.leaf 1 (Common.fact 288).pointIds 288), (.leaf 2 (Common.fact 289).pointIds 289), (.leaf 3 (Common.fact 290).pointIds 290), (.leaf 4 (Common.fact 613).pointIds 613), (.leaf 5 (Common.fact 291).pointIds 291), B0207]
theorem treeEq0206 : B0206.tree = HexagonCover.NBand.M7700_7900.SplitData.node0206 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0207

theorem accepted0206 : B0206.accepted = true := by decide +kernel
theorem checked0206 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7700_7900.SplitData.node0206 (maskNeeds ![10387129018270111715863986064851329, 302232535767567862597122, 2425782874489825007620, 79266848140492005727134572552, 185720606013363029522709461774615554621805002768, 42535295865117307932921825928971419680, 21778071483256974387270895952471420043328]) := by
  rw [← treeEq0206]
  exact B0206.sound accepted0206
#print axioms checked0206

end HexagonCover.NBand.M7700_7900.SplitTree.Run0001
