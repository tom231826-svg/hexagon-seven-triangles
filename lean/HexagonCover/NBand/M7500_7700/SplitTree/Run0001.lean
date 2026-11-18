import HexagonCover.NBand.M7500_7700.SplitData
import HexagonCover.NBand.M7500_7700.SplitTree.Run0000
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7500_7700.SplitTree.Run0001
open OwnerTree HexagonCover.NBand.M7500_7700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1005) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def B0182 : Block := .branch 170 ![10385861367669883486462489361645953, 618970019642690137449563650, 77919046967349146032132, 5846006549663894039735755165580962022322679603208, 182699203488105857128017958444269711768393187344, 233840261972987002208454690542538204970878178295840, 22479903864714961470063917021614029930560] ![(.leaf 0 (Common.fact 572).pointIds 572), (.leaf 1 (Common.fact 537).pointIds 537), (.leaf 2 (Common.fact 531).pointIds 531), (.leaf 3 (Common.fact 573).pointIds 573), (.leaf 4 (Common.fact 574).pointIds 574), (.leaf 5 (Common.fact 575).pointIds 575), (.leaf 6 (Common.fact 576).pointIds 576)]
theorem treeEq0182 : B0182.tree = HexagonCover.NBand.M7500_7700.SplitData.node0182 := by
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
  · rfl

def B0181 : Block := .branch 113 ![1267650600228229401496703205761, 618970019642690137449563650, 77919046967349146032132, 5846006549663894039735755165580962022322679603208, 182699203488105857128017958444269711768393187344, 233840261972987002208454690542538204970878178295840, 27924422059968530543904637523678341890112] ![B0182, (.leaf 1 (Common.fact 240).pointIds 240), (.leaf 2 (Common.fact 241).pointIds 241), (.leaf 3 (Common.fact 242).pointIds 242), (.leaf 4 (Common.fact 243).pointIds 243), (.leaf 5 (Common.fact 244).pointIds 244), (.leaf 6 (Common.fact 571).pointIds 571)]
theorem treeEq0181 : B0181.tree = HexagonCover.NBand.M7500_7700.SplitData.node0181 := by
  change Tree.branch (113 : Fin 173) _ = Tree.branch (113 : Fin 173) _
  apply congrArg (Tree.branch (113 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0182
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0180 : Block := .branch 143 ![1267650600228229401496703205761, 618970019642690137449563650, 77919046967349146032132, 5846006549663894039735755165580962022322679603208, 182688053115506591816447190585133387587640197136, 233840261972987002208454690542538204970878178295840, 27924422059968530543904637523678341890112] ![(.leaf 0 (Common.fact 565).pointIds 565), (.leaf 1 (Common.fact 566).pointIds 566), (.leaf 2 (Common.fact 567).pointIds 567), (.leaf 3 (Common.fact 568).pointIds 568), B0181, (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 570).pointIds 570)]
theorem treeEq0180 : B0180.tree = HexagonCover.NBand.M7500_7700.SplitData.node0180 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0181
  · rfl
  · rfl

def B0179 : Block := .branch 128 ![1267650600228229401496703205761, 618970019642690137449563650, 77919046967349146032132, 5846006549323611672814816702117587414890911391752, 185545336094068327906456454488816458905593937936, 233840261972987002208454690542538204970878178295840, 27924422060285443193961694874052517691456] ![(.leaf 0 (Common.fact 291).pointIds 291), (.leaf 1 (Common.fact 292).pointIds 292), (.leaf 2 (Common.fact 293).pointIds 293), B0180, (.leaf 4 (Common.fact 563).pointIds 563), (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 6 (Common.fact 564).pointIds 564)]
theorem treeEq0179 : B0179.tree = HexagonCover.NBand.M7500_7700.SplitData.node0179 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0180
  · rfl
  · rfl
  · rfl

def B0178 : Block := .branch 129 ![1267650600228229401496703205761, 618970019642690137449563650, 77919046967349146032132, 5846006549323611672894044864631851752484455342088, 185545336094068327906456454488816458905593937936, 233840261972987002208454690542538204970878178295840, 27243857326443566267034945659188981268544] ![(.leaf 0 (Common.fact 259).pointIds 259), (.leaf 1 (Common.fact 260).pointIds 260), (.leaf 2 (Common.fact 261).pointIds 261), (.leaf 3 (Common.fact 262).pointIds 262), (.leaf 4 (Common.fact 562).pointIds 562), (.leaf 5 (Common.fact 263).pointIds 263), B0179]
theorem treeEq0178 : B0178.tree = HexagonCover.NBand.M7500_7700.SplitData.node0178 := by
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
  · exact treeEq0179

def B0177 : Block := .branch 130 ![1267650600228229401496703205761, 618970019642690137449563650, 77919046967349146032132, 5846006549323611672894044864631851752484455342088, 185545336094068327906456454488816458905593937936, 233840261972987002208454690542538204970878178295840, 27243857326443566267034945659188981268544] ![(.leaf 0 (Common.fact 252).pointIds 252), (.leaf 1 (Common.fact 253).pointIds 253), (.leaf 2 (Common.fact 254).pointIds 254), (.leaf 3 (Common.fact 255).pointIds 255), (.leaf 4 (Common.fact 561).pointIds 561), (.leaf 5 (Common.fact 256).pointIds 256), B0178]
theorem treeEq0177 : B0177.tree = HexagonCover.NBand.M7500_7700.SplitData.node0177 := by
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
  · exact treeEq0178

def B0176 : Block := .branch 131 ![1267650600228229401496703205761, 618970019642690137449563650, 77919046967349146032132, 5846006549323611672894044864631851752484455342088, 185545336094068327906456454488816458905593937936, 233840261972987002208454690542538204970878178295840, 27243857326443566267034945659188981268544] ![(.leaf 0 (Common.fact 555).pointIds 555), (.leaf 1 (Common.fact 556).pointIds 556), (.leaf 2 (Common.fact 557).pointIds 557), (.leaf 3 (Common.fact 558).pointIds 558), (.leaf 4 (Common.fact 559).pointIds 559), (.leaf 5 (Common.fact 560).pointIds 560), B0177]
theorem treeEq0176 : B0176.tree = HexagonCover.NBand.M7500_7700.SplitData.node0176 := by
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
  · exact treeEq0177

def B0175 : Block := .branch 162 ![1267650600228229401496703205761, 618970019642690137449563650, 77919046967349146032132, 79305533766719673860725170184, 185545336094068327906456454488816458905593937936, 233840261972987002208454690542538204970878178295840, 27243857326443566267034945659188981268544] ![(.leaf 0 (Common.fact 372).pointIds 372), (.leaf 1 (Common.fact 373).pointIds 373), (.leaf 2 (Common.fact 374).pointIds 374), B0176, (.leaf 4 (Common.fact 554).pointIds 554), (.leaf 5 (Common.fact 375).pointIds 375), (.leaf 6 (Common.fact 497).pointIds 497)]
theorem treeEq0175 : B0175.tree = HexagonCover.NBand.M7500_7700.SplitData.node0175 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0176
  · rfl
  · rfl
  · rfl

def B0174 : Block := .branch 165 ![1267650600228229401496703205761, 618970019642690137449563650, 77919046967349146032132, 79305533766719673860725170184, 185545336094068327906456454488816458905593937936, 187072209578398108825936775895617148341888336920608, 27243857326443566267034945659188981268544] ![(.leaf 0 (Common.fact 377).pointIds 377), (.leaf 1 (Common.fact 378).pointIds 378), (.leaf 2 (Common.fact 379).pointIds 379), (.leaf 3 (Common.fact 380).pointIds 380), (.leaf 4 (Common.fact 553).pointIds 553), B0175, (.leaf 0 [] 0)]
theorem treeEq0174 : B0174.tree = HexagonCover.NBand.M7500_7700.SplitData.node0174 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0175
  · rfl

def B0173 : Block := .branch 167 ![1267650600228229401496703205761, 618970019642690137449563650, 77919046967349146032132, 79305533766719673860725170184, 185545336094068327906456454488816458905593937936, 42535295865117307932921825928971419680, 27243857326443566267034945659188981268544] ![(.leaf 0 (Common.fact 547).pointIds 547), (.leaf 1 (Common.fact 548).pointIds 548), (.leaf 2 (Common.fact 549).pointIds 549), (.leaf 3 (Common.fact 550).pointIds 550), (.leaf 4 (Common.fact 551).pointIds 551), B0174, (.leaf 6 (Common.fact 552).pointIds 552)]
theorem treeEq0173 : B0173.tree = HexagonCover.NBand.M7500_7700.SplitData.node0173 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0174
  · rfl

def B0172 : Block := .branch 151 ![1267650600228229401496703205761, 618970019642690137449563650, 77919046967349146032132, 79305533766719673860725170184, 182690840708656408144339882549917468632828444688, 42535295865117307932921825928971419680, 27243857326443566267034945659188981268544] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), B0173, (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 546).pointIds 546)]
theorem treeEq0172 : B0172.tree = HexagonCover.NBand.M7500_7700.SplitData.node0172 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0173
  · rfl
  · rfl

theorem accepted0172 : B0172.accepted = true := by decide +kernel
theorem checked0172 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node0172 (maskNeeds ![1267650600228229401496703205761, 618970019642690137449563650, 77919046967349146032132, 79305533766719673860725170184, 182690840708656408144339882549917468632828444688, 42535295865117307932921825928971419680, 27243857326443566267034945659188981268544]) := by
  rw [← treeEq0172]
  exact B0172.sound accepted0172
#print axioms checked0172

def Tip0142_0150 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node0150 ![5193564509135055857931993032425857, 1461501637330902918204303802735925709793382106626, 77937529740219874547716, 174224571863520609350126482009466096082952, 11874700803313586534923492924246526317860472586256, 42535295865117307932921825928971419680, 2854522629268921687129180547117866305726185536] HexagonCover.NBand.M7500_7700.SplitTree.Run0000.checked0150
def Tip0142_0172 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node0172 ![1267650600228229401496703205761, 618970019642690137449563650, 77919046967349146032132, 79305533766719673860725170184, 182690840708656408144339882549917468632828444688, 42535295865117307932921825928971419680, 27243857326443566267034945659188981268544] checked0172
def B0169 : Block := .branch 171 ![5193564509135055857931993032425857, 618970019642690137449563650, 1461501637330902918203684835077466261090755155972, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 1496577676626844588240573268701473812127674924400672, 2854517184751050952113765133124147397434802240] ![(.leaf 0 (Common.fact 539).pointIds 539), (.leaf 1 (Common.fact 540).pointIds 540), (.leaf 2 (Common.fact 541).pointIds 541), (.leaf 3 (Common.fact 529).pointIds 529), (.leaf 4 (Common.fact 535).pointIds 535), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 515).pointIds 515)]
theorem treeEq0169 : B0169.tree = HexagonCover.NBand.M7500_7700.SplitData.node0169 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0168 : Block := .branch 170 ![5193564509135055857931993032425857, 618970019642690137449563650, 1461501637330902918203684835077466261090755155972, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 393248, 2854517184751050952113765133124147397434802240] ![(.leaf 0 (Common.fact 536).pointIds 536), (.leaf 1 (Common.fact 537).pointIds 537), (.leaf 2 (Common.fact 538).pointIds 538), (.leaf 3 (Common.fact 527).pointIds 527), (.leaf 4 (Common.fact 525).pointIds 525), B0169, (.leaf 6 (Common.fact 508).pointIds 508)]
theorem treeEq0168 : B0168.tree = HexagonCover.NBand.M7500_7700.SplitData.node0168 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0169
  · rfl

def B0149 : Block := .branch 160 ![5193564509135055857931993032425857, 618970019642690137449563650, 77937529740219874547716, 174224571863520609350126482009466096082952, 11874700803313586534923492924246526317860472586256, 42535295865117307932921825928971419680, 2854522629268921687129180547117866305726185536] ![(.leaf 0 (Common.fact 362).pointIds 362), Tip0142_0150, B0168, (.leaf 3 (Common.fact 363).pointIds 363), (.leaf 4 (Common.fact 364).pointIds 364), (.leaf 5 (Common.fact 365).pointIds 365), (.leaf 6 (Common.fact 489).pointIds 489)]
theorem treeEq0149 : B0149.tree = HexagonCover.NBand.M7500_7700.SplitData.node0149 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0168
  · rfl
  · rfl
  · rfl
  · rfl

def B0171 : Block := .branch 171 ![1267650600228229401496703205761, 618970019642690137449563650, 77919046967349146032132, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 1496577676626844588240573268701473812127674924400672, 2854517184756243248972299960752677893764022336] ![(.leaf 0 (Common.fact 544).pointIds 544), (.leaf 1 (Common.fact 540).pointIds 540), (.leaf 2 (Common.fact 533).pointIds 533), (.leaf 3 (Common.fact 529).pointIds 529), (.leaf 4 (Common.fact 535).pointIds 535), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 545).pointIds 545)]
theorem treeEq0171 : B0171.tree = HexagonCover.NBand.M7500_7700.SplitData.node0171 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0170 : Block := .branch 170 ![1267650600228229401496703205761, 618970019642690137449563650, 77919046967349146032132, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 393248, 2854517184756243248972299960752677893764022336] ![(.leaf 0 (Common.fact 542).pointIds 542), (.leaf 1 (Common.fact 537).pointIds 537), (.leaf 2 (Common.fact 531).pointIds 531), (.leaf 3 (Common.fact 527).pointIds 527), (.leaf 4 (Common.fact 525).pointIds 525), B0171, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq0170 : B0170.tree = HexagonCover.NBand.M7500_7700.SplitData.node0170 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0171
  · rfl

def B0148 : Block := .branch 112 ![1267650600228229401496703205761, 618970019642690137449563650, 77937529740219874547716, 174224571863520609350126482009466096082952, 11874700803313586534923492924246526317860472586256, 42535295865117307932921825928971419680, 2854522629268921687129180547117866305726185536] ![B0149, (.leaf 1 (Common.fact 484).pointIds 484), (.leaf 2 (Common.fact 485).pointIds 485), (.leaf 3 (Common.fact 486).pointIds 486), (.leaf 4 (Common.fact 487).pointIds 487), (.leaf 5 (Common.fact 488).pointIds 488), B0170]
theorem treeEq0148 : B0148.tree = HexagonCover.NBand.M7500_7700.SplitData.node0148 := by
  change Tree.branch (112 : Fin 173) _ = Tree.branch (112 : Fin 173) _
  apply congrArg (Tree.branch (112 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0149
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0170

def B0147 : Block := .branch 137 ![1267650600228229401496703205761, 618970019642690137449563650, 77937529740219874547716, 116056878683004400771817480, 11874700803313586534923492924246526317860472586256, 42535295865117307932921825928971419680, 2854522629268921687129180547117866305726185536] ![(.leaf 0 (Common.fact 286).pointIds 286), (.leaf 1 (Common.fact 287).pointIds 287), (.leaf 2 (Common.fact 288).pointIds 288), B0148, (.leaf 4 (Common.fact 483).pointIds 483), (.leaf 5 (Common.fact 290).pointIds 290), (.leaf 0 [] 0)]
theorem treeEq0147 : B0147.tree = HexagonCover.NBand.M7500_7700.SplitData.node0147 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0148
  · rfl
  · rfl
  · rfl

def B0146 : Block := .branch 163 ![1267650600228229401496703205761, 618970019642690137449563650, 77937529740219874547716, 116056878683004400771817480, 182687704666363189294014262516262160613012242448, 42535295865117307932921825928971419680, 2854522629268921687129180547117866305726185536] ![(.leaf 0 (Common.fact 280).pointIds 280), (.leaf 1 (Common.fact 281).pointIds 281), (.leaf 2 (Common.fact 282).pointIds 282), (.leaf 3 (Common.fact 283).pointIds 283), B0147, (.leaf 5 (Common.fact 284).pointIds 284), (.leaf 6 (Common.fact 482).pointIds 482)]
theorem treeEq0146 : B0146.tree = HexagonCover.NBand.M7500_7700.SplitData.node0146 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0147
  · rfl
  · rfl

def B0145 : Block := .branch 151 ![1267650600228229401496703205761, 618970019642690137449563650, 77937529740219874547716, 116056878683004400771817480, 182687704666363189294014262516262160613012242448, 42535295865117307932921825928971419680, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 481).pointIds 481), (.leaf 5 (Common.fact 277).pointIds 277), B0146]
theorem treeEq0145 : B0145.tree = HexagonCover.NBand.M7500_7700.SplitData.node0145 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0146

def B0144 : Block := .branch 108 ![1267650600228229401496703205761, 618970019642690137449563650, 77937529740219874547716, 79363562206061176061111066632, 182690840708656408144339882549917468632828444688, 42535295865117307932921825928971419680, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 316).pointIds 316), (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), B0145, (.leaf 5 (Common.fact 320).pointIds 320), Tip0142_0172]
theorem treeEq0144 : B0144.tree = HexagonCover.NBand.M7500_7700.SplitData.node0144 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0145
  · rfl
  · rfl

def B0186 : Block := .branch 142 ![385, 1538, 6148, 24584, 182690492259512843362630125267682850080190201872, 393248, 11692013125891080347554491270338483033280421036096] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), (.leaf 4 (Common.fact 580).pointIds 580), (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 581).pointIds 581)]
theorem treeEq0186 : B0186.tree = HexagonCover.NBand.M7500_7700.SplitData.node0186 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0185 : Block := .branch 163 ![385, 1538, 6148, 24584, 182690492259512843362630125267682850080190201872, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 280).pointIds 280), (.leaf 1 (Common.fact 281).pointIds 281), (.leaf 2 (Common.fact 282).pointIds 282), (.leaf 3 (Common.fact 283).pointIds 283), (.leaf 4 (Common.fact 579).pointIds 579), (.leaf 5 (Common.fact 284).pointIds 284), B0186]
theorem treeEq0185 : B0185.tree = HexagonCover.NBand.M7500_7700.SplitData.node0185 := by
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
  · exact treeEq0186

def B0184 : Block := .branch 165 ![385, 1538, 6148, 24584, 182690492259512843362630125267682850080190201872, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 377).pointIds 377), (.leaf 1 (Common.fact 378).pointIds 378), (.leaf 2 (Common.fact 379).pointIds 379), (.leaf 3 (Common.fact 380).pointIds 380), (.leaf 4 (Common.fact 578).pointIds 578), B0185, (.leaf 0 [] 0)]
theorem treeEq0184 : B0184.tree = HexagonCover.NBand.M7500_7700.SplitData.node0184 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0185
  · rfl

def B0183 : Block := .branch 167 ![385, 1538, 6148, 24584, 182690492259512843362630125267682850080190201872, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 547).pointIds 547), (.leaf 1 (Common.fact 548).pointIds 548), (.leaf 2 (Common.fact 549).pointIds 549), (.leaf 3 (Common.fact 550).pointIds 550), (.leaf 4 (Common.fact 577).pointIds 577), B0184, (.leaf 6 (Common.fact 552).pointIds 552)]
theorem treeEq0183 : B0183.tree = HexagonCover.NBand.M7500_7700.SplitData.node0183 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0184
  · rfl

def B0143 : Block := .branch 107 ![1267650600228229401496703205761, 618970019642690137449563650, 77937529740219874547716, 79363562206061176061111066632, 182690840708656408144339882549917468632828444688, 42535295865117307932921825928971419680, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 303).pointIds 303), (.leaf 1 (Common.fact 304).pointIds 304), (.leaf 2 (Common.fact 305).pointIds 305), B0144, B0183, (.leaf 5 (Common.fact 307).pointIds 307), (.leaf 6 (Common.fact 480).pointIds 480)]
theorem treeEq0143 : B0143.tree = HexagonCover.NBand.M7500_7700.SplitData.node0143 := by
  change Tree.branch (107 : Fin 173) _ = Tree.branch (107 : Fin 173) _
  apply congrArg (Tree.branch (107 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0144
  · exact treeEq0183
  · rfl
  · rfl

def B0188 : Block := .branch 171 ![1237940039285380274899124609, 618970019642690137449563650, 77919046967349146032132, 158533696280984011454269120520, 182690840708656408144339882549917468632828444688, 1496577676626844588240573268701473812127674924400672, 27243857003192663208836448277529663897664] ![(.leaf 0 (Common.fact 586).pointIds 586), (.leaf 1 (Common.fact 540).pointIds 540), (.leaf 2 (Common.fact 533).pointIds 533), (.leaf 3 (Common.fact 587).pointIds 587), (.leaf 4 (Common.fact 588).pointIds 588), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 589).pointIds 589)]
theorem treeEq0188 : B0188.tree = HexagonCover.NBand.M7500_7700.SplitData.node0188 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0187 : Block := .branch 170 ![1237940039285380274899124609, 618970019642690137449563650, 77919046967349146032132, 158533696280984011454269120520, 182690840708656408144339882549917468632828444688, 393248, 27243857003192663208836448277529663897664] ![(.leaf 0 (Common.fact 582).pointIds 582), (.leaf 1 (Common.fact 537).pointIds 537), (.leaf 2 (Common.fact 531).pointIds 531), (.leaf 3 (Common.fact 583).pointIds 583), (.leaf 4 (Common.fact 584).pointIds 584), B0188, (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq0187 : B0187.tree = HexagonCover.NBand.M7500_7700.SplitData.node0187 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0188
  · rfl

def B0142 : Block := .branch 100 ![1237940039285380274899124609, 618970019642690137449563650, 77937529740219874547716, 237819887234589851248198967304, 182690840708656408144339882549917468632828444688, 42535295865117307932921825928971419680, 27243857001925012608608218876032960692288] ![B0143, (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), B0187]
theorem treeEq0142 : B0142.tree = HexagonCover.NBand.M7500_7700.SplitData.node0142 := by
  change Tree.branch (100 : Fin 173) _ = Tree.branch (100 : Fin 173) _
  apply congrArg (Tree.branch (100 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0143
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0187

theorem accepted0142 : B0142.accepted = true := by decide +kernel
theorem checked0142 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node0142 (maskNeeds ![1237940039285380274899124609, 618970019642690137449563650, 77937529740219874547716, 237819887234589851248198967304, 182690840708656408144339882549917468632828444688, 42535295865117307932921825928971419680, 27243857001925012608608218876032960692288]) := by
  rw [← treeEq0142]
  exact B0142.sound accepted0142
#print axioms checked0142

def Tip0139_0142 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node0142 ![1237940039285380274899124609, 618970019642690137449563650, 77937529740219874547716, 237819887234589851248198967304, 182690840708656408144339882549917468632828444688, 42535295865117307932921825928971419680, 27243857001925012608608218876032960692288] checked0142
def B0192 : Block := .branch 142 ![385, 1538, 6148, 24584, 182687704666362864933916929118064052644079566864, 393248, 11692013125891080347554491270338483033280421036096] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), (.leaf 4 (Common.fact 593).pointIds 593), (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 581).pointIds 581)]
theorem treeEq0192 : B0192.tree = HexagonCover.NBand.M7500_7700.SplitData.node0192 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0191 : Block := .branch 163 ![385, 1538, 6148, 24584, 182687704666362864933916929118064052644079566864, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 280).pointIds 280), (.leaf 1 (Common.fact 281).pointIds 281), (.leaf 2 (Common.fact 282).pointIds 282), (.leaf 3 (Common.fact 283).pointIds 283), (.leaf 4 (Common.fact 592).pointIds 592), (.leaf 5 (Common.fact 284).pointIds 284), B0192]
theorem treeEq0191 : B0191.tree = HexagonCover.NBand.M7500_7700.SplitData.node0191 := by
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
  · exact treeEq0192

def B0190 : Block := .branch 165 ![385, 1538, 6148, 24584, 182687704666362864933916929118064052644079566864, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 377).pointIds 377), (.leaf 1 (Common.fact 378).pointIds 378), (.leaf 2 (Common.fact 379).pointIds 379), (.leaf 3 (Common.fact 380).pointIds 380), (.leaf 4 (Common.fact 591).pointIds 591), B0191, (.leaf 0 [] 0)]
theorem treeEq0190 : B0190.tree = HexagonCover.NBand.M7500_7700.SplitData.node0190 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0191
  · rfl

def B0189 : Block := .branch 167 ![385, 1538, 6148, 24584, 182687704666362864933916929118064052644079566864, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 547).pointIds 547), (.leaf 1 (Common.fact 548).pointIds 548), (.leaf 2 (Common.fact 549).pointIds 549), (.leaf 3 (Common.fact 550).pointIds 550), (.leaf 4 (Common.fact 590).pointIds 590), B0190, (.leaf 6 (Common.fact 552).pointIds 552)]
theorem treeEq0189 : B0189.tree = HexagonCover.NBand.M7500_7700.SplitData.node0189 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0190
  · rfl

def B0141 : Block := .branch 97 ![1237940039285380274899124609, 618970019642690137449563650, 77937529740219874547716, 79363562206061176061111066632, 182690840708656408144339882549917468632828444688, 42535295865117307932921825928971419680, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 309).pointIds 309), (.leaf 1 (Common.fact 310).pointIds 310), (.leaf 2 (Common.fact 311).pointIds 311), Tip0139_0142, B0189, (.leaf 5 (Common.fact 313).pointIds 313), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq0141 : B0141.tree = HexagonCover.NBand.M7500_7700.SplitData.node0141 := by
  change Tree.branch (97 : Fin 173) _ = Tree.branch (97 : Fin 173) _
  apply congrArg (Tree.branch (97 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0189
  · rfl
  · rfl

def B0200 : Block := .branch 171 ![748288838313422294120286634955199815871152049357185, 618970019642690137449563650, 77919046967349146032132, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 1496577676626844588240573268701473812127674924400672, 2854517184751050953042220162588182603609145408] ![(.leaf 0 (Common.fact 602).pointIds 602), (.leaf 1 (Common.fact 540).pointIds 540), (.leaf 2 (Common.fact 533).pointIds 533), (.leaf 3 (Common.fact 529).pointIds 529), (.leaf 4 (Common.fact 535).pointIds 535), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 603).pointIds 603)]
theorem treeEq0200 : B0200.tree = HexagonCover.NBand.M7500_7700.SplitData.node0200 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0199 : Block := .branch 170 ![748288838313422294120286634955199815871152049357185, 618970019642690137449563650, 77919046967349146032132, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 393248, 2854517184751050953042220162588182603609145408] ![(.leaf 0 (Common.fact 600).pointIds 600), (.leaf 1 (Common.fact 537).pointIds 537), (.leaf 2 (Common.fact 531).pointIds 531), (.leaf 3 (Common.fact 527).pointIds 527), (.leaf 4 (Common.fact 525).pointIds 525), B0200, (.leaf 6 (Common.fact 601).pointIds 601)]
theorem treeEq0199 : B0199.tree = HexagonCover.NBand.M7500_7700.SplitData.node0199 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0200
  · rfl

def B0198 : Block := .branch 108 ![748288838313422294120286634955199815871152049357185, 618970019642690137449563650, 77919046967349146032132, 174224571863599818169827632512992844734472, 11874700803313586210404939265819799534704452010000, 393248, 2854522629268921688057635576581901511900528704] ![(.leaf 0 (Common.fact 316).pointIds 316), (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), B0199, (.leaf 5 (Common.fact 320).pointIds 320), (.leaf 6 (Common.fact 599).pointIds 599)]
theorem treeEq0198 : B0198.tree = HexagonCover.NBand.M7500_7700.SplitData.node0198 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0199
  · rfl
  · rfl

def B0197 : Block := .branch 119 ![748288838313422294120286634955199815871152049357185, 618970019642690137449563650, 77919046967349146032132, 174224571863599818169827632512992844734472, 11874700803313586210404939265819799534704452010000, 393248, 2854522629268921688057635576581901511900528704] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), B0198, (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 598).pointIds 598)]
theorem treeEq0197 : B0197.tree = HexagonCover.NBand.M7500_7700.SplitData.node0197 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0198
  · rfl
  · rfl

def B0196 : Block := .branch 129 ![748288838313422294120286634955199815871152049357185, 618970019642690137449563650, 77919046967349146032132, 174224571863599818169827632512992844734472, 11874700803313586210404939265819799534704452010000, 393248, 2854522629268921688057635576581901511900528704] ![(.leaf 0 (Common.fact 259).pointIds 259), (.leaf 1 (Common.fact 260).pointIds 260), (.leaf 2 (Common.fact 261).pointIds 261), (.leaf 3 (Common.fact 262).pointIds 262), B0197, (.leaf 5 (Common.fact 263).pointIds 263), (.leaf 6 (Common.fact 597).pointIds 597)]
theorem treeEq0196 : B0196.tree = HexagonCover.NBand.M7500_7700.SplitData.node0196 := by
  change Tree.branch (129 : Fin 173) _ = Tree.branch (129 : Fin 173) _
  apply congrArg (Tree.branch (129 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0197
  · rfl
  · rfl

def B0195 : Block := .branch 137 ![748288838313422294120286634955199815871152049357185, 618970019642690137449563650, 77919046967349146032132, 79324876579833507927520469000, 11874700803313586210404939265819799534704452010000, 393248, 2854522629268921688057635576581901511900528704] ![(.leaf 0 (Common.fact 286).pointIds 286), (.leaf 1 (Common.fact 287).pointIds 287), (.leaf 2 (Common.fact 288).pointIds 288), B0196, (.leaf 4 (Common.fact 596).pointIds 596), (.leaf 5 (Common.fact 290).pointIds 290), (.leaf 0 [] 0)]
theorem treeEq0195 : B0195.tree = HexagonCover.NBand.M7500_7700.SplitData.node0195 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0196
  · rfl
  · rfl
  · rfl

def B0194 : Block := .branch 151 ![748288838313422294120286634955199815871152049357185, 618970019642690137449563650, 77919046967349146032132, 79324876579833507927520469000, 11874700803313586210404939265819799534704452010000, 42535295865117307932921825928971419680, 27243857001925941063637682911239135035456] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 595).pointIds 595), (.leaf 5 (Common.fact 277).pointIds 277), B0195]
theorem treeEq0194 : B0194.tree = HexagonCover.NBand.M7500_7700.SplitData.node0194 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0195

def B0193 : Block := .branch 163 ![748288838313422294120286634955199815871152049357185, 618970019642690137449563650, 77919046967349146032132, 79324876579833507927520469000, 182687704666362864775460604089535377456991666192, 42535295865117307932921825928971419680, 27243857001925941063637682911239135035456] ![(.leaf 0 (Common.fact 280).pointIds 280), (.leaf 1 (Common.fact 281).pointIds 281), (.leaf 2 (Common.fact 282).pointIds 282), (.leaf 3 (Common.fact 283).pointIds 283), B0194, (.leaf 5 (Common.fact 284).pointIds 284), (.leaf 6 (Common.fact 594).pointIds 594)]
theorem treeEq0193 : B0193.tree = HexagonCover.NBand.M7500_7700.SplitData.node0193 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0194
  · rfl
  · rfl

def B0140 : Block := .branch 90 ![748288838313422294120286634955199815871152049357185, 618970019642690137449563650, 77937529740219874547716, 79363562206061176061111066632, 182690840708656408144339882549917468632828444688, 42535295865117307932921825928971419680, 27243857001925012608608218876032960692288] ![B0141, (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), B0193]
theorem treeEq0140 : B0140.tree = HexagonCover.NBand.M7500_7700.SplitData.node0140 := by
  change Tree.branch (90 : Fin 173) _ = Tree.branch (90 : Fin 173) _
  apply congrArg (Tree.branch (90 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0141
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0193

def B0202 : Block := .branch 171 ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 77919046967349146032132, 77371252455336267181219848, 182690840708656408144339882549917468632828444688, 1496577676626844588240573268701473812127674924400672, 27243857001925322093618040221101685473344] ![(.leaf 0 (Common.fact 602).pointIds 602), (.leaf 1 (Common.fact 607).pointIds 607), (.leaf 2 (Common.fact 533).pointIds 533), (.leaf 3 (Common.fact 608).pointIds 608), (.leaf 4 (Common.fact 588).pointIds 588), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 609).pointIds 609)]
theorem treeEq0202 : B0202.tree = HexagonCover.NBand.M7500_7700.SplitData.node0202 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0201 : Block := .branch 170 ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 77919046967349146032132, 77371252455336267181219848, 182690840708656408144339882549917468632828444688, 393248, 27243857001925322093618040221101685473344] ![(.leaf 0 (Common.fact 600).pointIds 600), (.leaf 1 (Common.fact 604).pointIds 604), (.leaf 2 (Common.fact 531).pointIds 531), (.leaf 3 (Common.fact 605).pointIds 605), (.leaf 4 (Common.fact 584).pointIds 584), B0202, (.leaf 6 (Common.fact 606).pointIds 606)]
theorem treeEq0201 : B0201.tree = HexagonCover.NBand.M7500_7700.SplitData.node0201 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0202
  · rfl

def B0139 : Block := .branch 89 ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 77937529740219874547716, 79363562206061176061111066632, 182690840708656408144339882549917468632828444688, 42535295865117307932921825928971419680, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 70).pointIds 70), B0140, (.leaf 2 (Common.fact 72).pointIds 72), (.leaf 3 (Common.fact 73).pointIds 73), (.leaf 4 (Common.fact 74).pointIds 74), (.leaf 5 (Common.fact 75).pointIds 75), B0201]
theorem treeEq0139 : B0139.tree = HexagonCover.NBand.M7500_7700.SplitData.node0139 := by
  change Tree.branch (89 : Fin 173) _ = Tree.branch (89 : Fin 173) _
  apply congrArg (Tree.branch (89 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0140
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0201

theorem accepted0139 : B0139.accepted = true := by decide +kernel
theorem checked0139 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node0139 (maskNeeds ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 77937529740219874547716, 79363562206061176061111066632, 182690840708656408144339882549917468632828444688, 42535295865117307932921825928971419680, 27243857001925012608608218876032960692288]) := by
  rw [← treeEq0139]
  exact B0139.sound accepted0139
#print axioms checked0139

def B0228 : Block := .branch 170 ![748288838313422304507415653225311531735138114208129, 302231526961251331606018, 40177008592539403425796, 5846006549663894039735755165580962022322679603208, 182699203488105857128017958444269711768393187344, 233840261972987002208454690542538204970878178295840, 22479903864714497318107048729925266178112] ![(.leaf 0 (Common.fact 633).pointIds 633), (.leaf 1 (Common.fact 604).pointIds 604), (.leaf 2 (Common.fact 634).pointIds 634), (.leaf 3 (Common.fact 573).pointIds 573), (.leaf 4 (Common.fact 574).pointIds 574), (.leaf 5 (Common.fact 575).pointIds 575), (.leaf 6 (Common.fact 635).pointIds 635)]
theorem treeEq0228 : B0228.tree = HexagonCover.NBand.M7500_7700.SplitData.node0228 := by
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
  · rfl

def B0227 : Block := .branch 86 ![748288838313422304507415653225311531735138114208129, 302231526961251331606018, 40195491365410131941380, 5846006549663894039735677794328506686055498407944, 182699203488105857128017958444269711768393187344, 233840261972987002208454690542538204970878178295840, 27924421735766425383578099799207733362752] ![(.leaf 0 (Common.fact 357).pointIds 357), (.leaf 1 (Common.fact 358).pointIds 358), (.leaf 2 (Common.fact 359).pointIds 359), B0228, (.leaf 4 (Common.fact 360).pointIds 360), (.leaf 5 (Common.fact 361).pointIds 361), (.leaf 6 (Common.fact 632).pointIds 632)]
theorem treeEq0227 : B0227.tree = HexagonCover.NBand.M7500_7700.SplitData.node0227 := by
  change Tree.branch (86 : Fin 173) _ = Tree.branch (86 : Fin 173) _
  apply congrArg (Tree.branch (86 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0228
  · rfl
  · rfl
  · rfl

def B0226 : Block := .branch 101 ![748288838313422304504880352024855072932144707797377, 302231526961251331606018, 40195491365410131941380, 5846006549663894039735677794328506686055498407944, 182699203488105857128017958444269711768393187344, 233840261972987002208454690542538204970878178295840, 27924421735766425383578099799207733362752] ![B0227, (.leaf 1 (Common.fact 626).pointIds 626), (.leaf 2 (Common.fact 627).pointIds 627), (.leaf 3 (Common.fact 628).pointIds 628), (.leaf 4 (Common.fact 629).pointIds 629), (.leaf 5 (Common.fact 630).pointIds 630), (.leaf 6 (Common.fact 631).pointIds 631)]
theorem treeEq0226 : B0226.tree = HexagonCover.NBand.M7500_7700.SplitData.node0226 := by
  change Tree.branch (101 : Fin 173) _ = Tree.branch (101 : Fin 173) _
  apply congrArg (Tree.branch (101 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0227
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0225 : Block := .branch 113 ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 40195491365410131941380, 5846006549663894039735677794328506686055498407944, 182699203488105857128017958444269711768393187344, 233840261972987002208454690542538204970878178295840, 27924421735766425383578099799207733362752] ![B0226, (.leaf 1 (Common.fact 240).pointIds 240), (.leaf 2 (Common.fact 241).pointIds 241), (.leaf 3 (Common.fact 242).pointIds 242), (.leaf 4 (Common.fact 243).pointIds 243), (.leaf 5 (Common.fact 244).pointIds 244), (.leaf 6 (Common.fact 625).pointIds 625)]
theorem treeEq0225 : B0225.tree = HexagonCover.NBand.M7500_7700.SplitData.node0225 := by
  change Tree.branch (113 : Fin 173) _ = Tree.branch (113 : Fin 173) _
  apply congrArg (Tree.branch (113 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0226
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0224 : Block := .branch 143 ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 40195491365410131941380, 5846006549663894039735677794328506686055498407944, 182688053115506591816447190585133387587640197136, 233840261972987002208454690542538204970878178295840, 27924421735766425383578099799207733362752] ![(.leaf 0 (Common.fact 565).pointIds 565), (.leaf 1 (Common.fact 566).pointIds 566), (.leaf 2 (Common.fact 567).pointIds 567), (.leaf 3 (Common.fact 568).pointIds 568), B0225, (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 624).pointIds 624)]
theorem treeEq0224 : B0224.tree = HexagonCover.NBand.M7500_7700.SplitData.node0224 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0225
  · rfl
  · rfl

def B0223 : Block := .branch 128 ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 40195491365410131941380, 5846006549323611672814739330865132078623730196488, 185545336094068327906456454488816458905593937936, 233840261972987002208454690542538204970878178295840, 27924421735766889611092831816810820534336] ![(.leaf 0 (Common.fact 291).pointIds 291), (.leaf 1 (Common.fact 292).pointIds 292), (.leaf 2 (Common.fact 293).pointIds 293), B0224, (.leaf 4 (Common.fact 563).pointIds 563), (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 6 (Common.fact 564).pointIds 564)]
theorem treeEq0223 : B0223.tree = HexagonCover.NBand.M7500_7700.SplitData.node0223 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0224
  · rfl
  · rfl
  · rfl

def B0222 : Block := .branch 129 ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 40195491365410131941380, 5846006549323611672893967493379396416217274146824, 185545336094068327906456454488816458905593937936, 233840261972987002208454690542538204970878178295840, 27243857001925012684166082601947284111424] ![(.leaf 0 (Common.fact 259).pointIds 259), (.leaf 1 (Common.fact 260).pointIds 260), (.leaf 2 (Common.fact 261).pointIds 261), (.leaf 3 (Common.fact 262).pointIds 262), (.leaf 4 (Common.fact 562).pointIds 562), (.leaf 5 (Common.fact 263).pointIds 263), B0223]
theorem treeEq0222 : B0222.tree = HexagonCover.NBand.M7500_7700.SplitData.node0222 := by
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
  · exact treeEq0223

def B0221 : Block := .branch 130 ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 40195491365410131941380, 5846006549323611672893967493379396416217274146824, 185545336094068327906456454488816458905593937936, 233840261972987002208454690542538204970878178295840, 27243857001925012684166082601947284111424] ![(.leaf 0 (Common.fact 252).pointIds 252), (.leaf 1 (Common.fact 253).pointIds 253), (.leaf 2 (Common.fact 254).pointIds 254), (.leaf 3 (Common.fact 255).pointIds 255), (.leaf 4 (Common.fact 561).pointIds 561), (.leaf 5 (Common.fact 256).pointIds 256), B0222]
theorem treeEq0221 : B0221.tree = HexagonCover.NBand.M7500_7700.SplitData.node0221 := by
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
  · exact treeEq0222

def B0220 : Block := .branch 131 ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 40195491365410131941380, 5846006549323611672893967493379396416217274146824, 185545336094068327906456454488816458905593937936, 233840261972987002208454690542538204970878178295840, 27243857001925012684166082601947284111424] ![(.leaf 0 (Common.fact 555).pointIds 555), (.leaf 1 (Common.fact 556).pointIds 556), (.leaf 2 (Common.fact 557).pointIds 557), (.leaf 3 (Common.fact 558).pointIds 558), (.leaf 4 (Common.fact 559).pointIds 559), (.leaf 5 (Common.fact 560).pointIds 560), B0221]
theorem treeEq0220 : B0220.tree = HexagonCover.NBand.M7500_7700.SplitData.node0220 := by
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
  · exact treeEq0221

def B0219 : Block := .branch 162 ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 40195491365410131941380, 79228162514264337593543974920, 185545336094068327906456454488816458905593937936, 233840261972987002208454690542538204970878178295840, 27243857001925012684166082601947284111424] ![(.leaf 0 (Common.fact 372).pointIds 372), (.leaf 1 (Common.fact 373).pointIds 373), (.leaf 2 (Common.fact 374).pointIds 374), B0220, (.leaf 4 (Common.fact 554).pointIds 554), (.leaf 5 (Common.fact 375).pointIds 375), (.leaf 6 (Common.fact 497).pointIds 497)]
theorem treeEq0219 : B0219.tree = HexagonCover.NBand.M7500_7700.SplitData.node0219 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0220
  · rfl
  · rfl
  · rfl

def B0218 : Block := .branch 163 ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 40195491365410131941380, 79228162514264337593543974920, 185545336094068327906456454488816458905593937936, 233840261972987002208454690542538204970878178295840, 27243857001925012684166082601947284111424] ![(.leaf 0 (Common.fact 280).pointIds 280), (.leaf 1 (Common.fact 281).pointIds 281), (.leaf 2 (Common.fact 282).pointIds 282), (.leaf 3 (Common.fact 283).pointIds 283), (.leaf 4 (Common.fact 623).pointIds 623), (.leaf 5 (Common.fact 284).pointIds 284), B0219]
theorem treeEq0218 : B0218.tree = HexagonCover.NBand.M7500_7700.SplitData.node0218 := by
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
  · exact treeEq0219

def B0217 : Block := .branch 165 ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 40195491365410131941380, 79228162514264337593543974920, 185545336094068327906456454488816458905593937936, 187072209578398108825936775895617148341888336920608, 27243857001925012684166082601947284111424] ![(.leaf 0 (Common.fact 377).pointIds 377), (.leaf 1 (Common.fact 378).pointIds 378), (.leaf 2 (Common.fact 379).pointIds 379), (.leaf 3 (Common.fact 380).pointIds 380), (.leaf 4 (Common.fact 553).pointIds 553), B0218, (.leaf 0 [] 0)]
theorem treeEq0217 : B0217.tree = HexagonCover.NBand.M7500_7700.SplitData.node0217 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0218
  · rfl

def B0216 : Block := .branch 167 ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 40195491365410131941380, 79228162514264337593543974920, 185545336094068327906456454488816458905593937936, 42535295865117307932921825928971419680, 27243857001925012684166082601947284111424] ![(.leaf 0 (Common.fact 547).pointIds 547), (.leaf 1 (Common.fact 548).pointIds 548), (.leaf 2 (Common.fact 549).pointIds 549), (.leaf 3 (Common.fact 550).pointIds 550), (.leaf 4 (Common.fact 551).pointIds 551), B0217, (.leaf 6 (Common.fact 552).pointIds 552)]
theorem treeEq0216 : B0216.tree = HexagonCover.NBand.M7500_7700.SplitData.node0216 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0217
  · rfl

def B0215 : Block := .branch 151 ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 40195491365410131941380, 79228162514264337593543974920, 182690840708656408144339882549917468632828444688, 42535295865117307932921825928971419680, 27243857001925012684166082601947284111424] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), B0216, (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 622).pointIds 622)]
theorem treeEq0215 : B0215.tree = HexagonCover.NBand.M7500_7700.SplitData.node0215 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0216
  · rfl
  · rfl

theorem accepted0215 : B0215.accepted = true := by decide +kernel
theorem checked0215 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node0215 (maskNeeds ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 40195491365410131941380, 79228162514264337593543974920, 182690840708656408144339882549917468632828444688, 42535295865117307932921825928971419680, 27243857001925012684166082601947284111424]) := by
  rw [← treeEq0215]
  exact B0215.sound accepted0215
#print axioms checked0215

def Tip0137_0139 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node0139 ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 77937529740219874547716, 79363562206061176061111066632, 182690840708656408144339882549917468632828444688, 42535295865117307932921825928971419680, 27243857001925012608608218876032960692288] checked0139
def Tip0137_0215 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node0215 ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 40195491365410131941380, 79228162514264337593543974920, 182690840708656408144339882549917468632828444688, 42535295865117307932921825928971419680, 27243857001925012684166082601947284111424] checked0215
def B0214 : Block := .branch 171 ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 77919046967349146032132, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 1496577676626844588240573268701473812127674924400672, 2854517184751050635123743823611460756077805632] ![(.leaf 0 (Common.fact 602).pointIds 602), (.leaf 1 (Common.fact 607).pointIds 607), (.leaf 2 (Common.fact 533).pointIds 533), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 535).pointIds 535), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 621).pointIds 621)]
theorem treeEq0214 : B0214.tree = HexagonCover.NBand.M7500_7700.SplitData.node0214 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0213 : Block := .branch 170 ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 77919046967349146032132, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 393248, 2854517184751050635123743823611460756077805632] ![(.leaf 0 (Common.fact 600).pointIds 600), (.leaf 1 (Common.fact 604).pointIds 604), (.leaf 2 (Common.fact 531).pointIds 531), (.leaf 3 (Common.fact 618).pointIds 618), (.leaf 4 (Common.fact 525).pointIds 525), B0214, (.leaf 6 (Common.fact 619).pointIds 619)]
theorem treeEq0213 : B0213.tree = HexagonCover.NBand.M7500_7700.SplitData.node0213 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0214
  · rfl

def B0212 : Block := .branch 108 ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 77919046967349146032132, 174224571863758235809229933520046342037512, 11874700803313586210404939265819799534704452010000, 393248, 2854522629268921370139159237605179664369188928] ![(.leaf 0 (Common.fact 316).pointIds 316), (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), B0213, (.leaf 5 (Common.fact 320).pointIds 320), (.leaf 6 (Common.fact 617).pointIds 617)]
theorem treeEq0212 : B0212.tree = HexagonCover.NBand.M7500_7700.SplitData.node0212 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0213
  · rfl
  · rfl

def B0211 : Block := .branch 119 ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 77919046967349146032132, 174224571863758235809229933520046342037512, 11874700803313586210404939265819799534704452010000, 393248, 2854522629268921370139159237605179664369188928] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), B0212, (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 616).pointIds 616)]
theorem treeEq0211 : B0211.tree = HexagonCover.NBand.M7500_7700.SplitData.node0211 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0212
  · rfl
  · rfl

def B0210 : Block := .branch 129 ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 77919046967349146032132, 174224571863758235809229933520046342037512, 11874700803313586210404939265819799534704452010000, 393248, 2854522629268921370139159237605179664369188928] ![(.leaf 0 (Common.fact 259).pointIds 259), (.leaf 1 (Common.fact 260).pointIds 260), (.leaf 2 (Common.fact 261).pointIds 261), (.leaf 3 (Common.fact 262).pointIds 262), B0211, (.leaf 5 (Common.fact 263).pointIds 263), (.leaf 6 (Common.fact 615).pointIds 615)]
theorem treeEq0210 : B0210.tree = HexagonCover.NBand.M7500_7700.SplitData.node0210 := by
  change Tree.branch (129 : Fin 173) _ = Tree.branch (129 : Fin 173) _
  apply congrArg (Tree.branch (129 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0211
  · rfl
  · rfl

def B0209 : Block := .branch 97 ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 77937493711422855583748, 174224571863599779484201404844859254136840, 11874700803313586210404939265819799534704452010000, 393248, 2854522629268921687206551799573202572907380800] ![(.leaf 0 (Common.fact 309).pointIds 309), (.leaf 1 (Common.fact 310).pointIds 310), (.leaf 2 (Common.fact 311).pointIds 311), B0210, (.leaf 4 (Common.fact 592).pointIds 592), (.leaf 5 (Common.fact 313).pointIds 313), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq0209 : B0209.tree = HexagonCover.NBand.M7500_7700.SplitData.node0209 := by
  change Tree.branch (97 : Fin 173) _ = Tree.branch (97 : Fin 173) _
  apply congrArg (Tree.branch (97 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0210
  · rfl
  · rfl
  · rfl

def B0208 : Block := .branch 107 ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 77937493711422855583748, 174224571863599779484201404844859254136840, 11874700803313586210404939265819799534704452010000, 393248, 2854522629268921687206551799573202572907380800] ![(.leaf 0 (Common.fact 303).pointIds 303), (.leaf 1 (Common.fact 304).pointIds 304), (.leaf 2 (Common.fact 305).pointIds 305), B0209, (.leaf 4 (Common.fact 614).pointIds 614), (.leaf 5 (Common.fact 307).pointIds 307), (.leaf 6 (Common.fact 480).pointIds 480)]
theorem treeEq0208 : B0208.tree = HexagonCover.NBand.M7500_7700.SplitData.node0208 := by
  change Tree.branch (107 : Fin 173) _ = Tree.branch (107 : Fin 173) _
  apply congrArg (Tree.branch (107 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0209
  · rfl
  · rfl
  · rfl

def B0207 : Block := .branch 118 ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 77937493711422855583748, 174224571863599779484201404844859254136840, 11874700803313586210404939265819799534704452010000, 393248, 2854522629268921687206551799573202572907380800] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 298).pointIds 298), (.leaf 2 (Common.fact 299).pointIds 299), B0208, (.leaf 4 (Common.fact 612).pointIds 612), (.leaf 5 (Common.fact 301).pointIds 301), (.leaf 6 (Common.fact 613).pointIds 613)]
theorem treeEq0207 : B0207.tree = HexagonCover.NBand.M7500_7700.SplitData.node0207 := by
  change Tree.branch (118 : Fin 173) _ = Tree.branch (118 : Fin 173) _
  apply congrArg (Tree.branch (118 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0208
  · rfl
  · rfl
  · rfl

def B0206 : Block := .branch 128 ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 77937493711422855583748, 174224571863599779484201404844859254136840, 11874700803313586210404939265819799534704452010000, 393248, 2854522629268921687206551799573202572907380800] ![(.leaf 0 (Common.fact 291).pointIds 291), (.leaf 1 (Common.fact 292).pointIds 292), (.leaf 2 (Common.fact 293).pointIds 293), B0207, (.leaf 4 (Common.fact 611).pointIds 611), (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 6 (Common.fact 564).pointIds 564)]
theorem treeEq0206 : B0206.tree = HexagonCover.NBand.M7500_7700.SplitData.node0206 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0207
  · rfl
  · rfl
  · rfl

def B0205 : Block := .branch 137 ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 77937493711422855583748, 79286190953605839793929871368, 11874700803313586210404939265819799534704452010000, 393248, 2854522629268921687206551799573202572907380800] ![(.leaf 0 (Common.fact 286).pointIds 286), (.leaf 1 (Common.fact 287).pointIds 287), (.leaf 2 (Common.fact 288).pointIds 288), B0206, (.leaf 4 (Common.fact 596).pointIds 596), (.leaf 5 (Common.fact 290).pointIds 290), (.leaf 0 [] 0)]
theorem treeEq0205 : B0205.tree = HexagonCover.NBand.M7500_7700.SplitData.node0205 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0206
  · rfl
  · rfl
  · rfl

def B0204 : Block := .branch 151 ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 77937493711422855583748, 79286190953605839793929871368, 11874700803313586210404939265819799534704452010000, 42535295865117307932921825928971419680, 27243857001925089979860674212300141887552] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 595).pointIds 595), (.leaf 5 (Common.fact 277).pointIds 277), B0205]
theorem treeEq0204 : B0204.tree = HexagonCover.NBand.M7500_7700.SplitData.node0204 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0205

def B0203 : Block := .branch 163 ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 77937493711422855583748, 79286190953605839793929871368, 182687704666362864775460604089535377456991666192, 42535295865117307932921825928971419680, 27243857001925089979860674212300141887552] ![(.leaf 0 (Common.fact 280).pointIds 280), (.leaf 1 (Common.fact 281).pointIds 281), (.leaf 2 (Common.fact 282).pointIds 282), (.leaf 3 (Common.fact 283).pointIds 283), B0204, (.leaf 5 (Common.fact 284).pointIds 284), (.leaf 6 (Common.fact 610).pointIds 610)]
theorem treeEq0203 : B0203.tree = HexagonCover.NBand.M7500_7700.SplitData.node0203 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0204
  · rfl
  · rfl

def B0138 : Block := .branch 86 ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 77937529740219874547716, 79286190953605839793929871368, 182690840708656408144339882549917468632828444688, 42535295865117307932921825928971419680, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 357).pointIds 357), (.leaf 1 (Common.fact 358).pointIds 358), (.leaf 2 (Common.fact 359).pointIds 359), Tip0137_0139, (.leaf 4 (Common.fact 360).pointIds 360), (.leaf 5 (Common.fact 361).pointIds 361), B0203]
theorem treeEq0138 : B0138.tree = HexagonCover.NBand.M7500_7700.SplitData.node0138 := by
  change Tree.branch (86 : Fin 173) _ = Tree.branch (86 : Fin 173) _
  apply congrArg (Tree.branch (86 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0203

def B0137 : Block := .branch 76 ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 40195491365410131941380, 79286190953605839793929871368, 182690840708656408144339882549917468632828444688, 42535295865117307932921825928971419680, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), B0138, (.leaf 3 (Common.fact 327).pointIds 327), (.leaf 4 (Common.fact 328).pointIds 328), (.leaf 5 (Common.fact 329).pointIds 329), Tip0137_0215]
theorem treeEq0137 : B0137.tree = HexagonCover.NBand.M7500_7700.SplitData.node0137 := by
  change Tree.branch (76 : Fin 173) _ = Tree.branch (76 : Fin 173) _
  apply congrArg (Tree.branch (76 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0138
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0137 : B0137.accepted = true := by decide +kernel
theorem checked0137 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node0137 (maskNeeds ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 40195491365410131941380, 79286190953605839793929871368, 182690840708656408144339882549917468632828444688, 42535295865117307932921825928971419680, 27243857001925012608608218876032960692288]) := by
  rw [← treeEq0137]
  exact B0137.sound accepted0137
#print axioms checked0137

end HexagonCover.NBand.M7500_7700.SplitTree.Run0001
