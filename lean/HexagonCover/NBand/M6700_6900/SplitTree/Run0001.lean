import HexagonCover.NBand.M6700_6900.SplitData
import HexagonCover.NBand.M6700_6900.SplitTree.Run0000
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6700_6900.SplitTree.Run0001
open OwnerTree HexagonCover.NBand.M6700_6900

abbrev Block := Chunk (n := 175) (Certificate := Fin 929) (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck

def Tip0141_0147 : Block := .tip HexagonCover.NBand.M6700_6900.SplitData.node0147 ![63802945065326562128765061894766592385, 730750818665451459101842416358141510927477900802, 77919046967349146032132, 174224571863520570664500254341332505485320, 58642753197902479917441407571167582946850313961488, 5575186299632655785383929568162090376888352, 374144419183933736414135771130010210994987206180928] HexagonCover.NBand.M6700_6900.SplitTree.Run0000.checked0147
def B0167 : Block := .branch 171 ![63802945065326562128765061894766592385, 730750818665451459101842416358141510927477900802, 77919046967349146032132, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 46768057969775193015173700030850624791080218263584, 2619010934124200618774995364697211107841430867411008] ![(.leaf 0 (Common.fact 526).pointIds 526), (.leaf 1 (Common.fact 551).pointIds 551), (.leaf 2 (Common.fact 544).pointIds 544), (.leaf 3 (Common.fact 537).pointIds 537), (.leaf 4 (Common.fact 558).pointIds 558), (.leaf 5 (Common.fact 559).pointIds 559), (.leaf 6 (Common.fact 532).pointIds 532)]
theorem treeEq0167 : B0167.tree = HexagonCover.NBand.M6700_6900.SplitData.node0167 := by
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

def B0166 : Block := .branch 170 ![63802945065326562128765061894766592385, 730750818665451459101842416358141510927477900802, 77919046967349146032132, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 46768057969775193015173700030850624791080218263584, 1122433257497356030534422095995737295713755943403584] ![(.leaf 0 (Common.fact 520).pointIds 520), (.leaf 1 (Common.fact 549).pointIds 549), (.leaf 2 (Common.fact 542).pointIds 542), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 556).pointIds 556), (.leaf 5 (Common.fact 557).pointIds 557), B0167]
theorem treeEq0166 : B0166.tree = HexagonCover.NBand.M6700_6900.SplitData.node0166 := by
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
  · exact treeEq0167

def B0165 : Block := .branch 169 ![63802945065326562128765061894766592385, 730750818665451459101842416358141510927477900802, 77919046967349146032132, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 46768057969775193015173700030850624791080218263584, 374144419183933736414135461645000389649918481399872] ![(.leaf 0 (Common.fact 514).pointIds 514), (.leaf 1 (Common.fact 547).pointIds 547), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 533).pointIds 533), (.leaf 4 (Common.fact 554).pointIds 554), (.leaf 5 (Common.fact 555).pointIds 555), B0166]
theorem treeEq0165 : B0165.tree = HexagonCover.NBand.M6700_6900.SplitData.node0165 := by
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
  · exact treeEq0166

def B0146 : Block := .branch 165 ![63802945065326562128765061894766592385, 730750818665451459101842416358141510927477900802, 77919046967349146032132, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 5575186299632655785383929568162090376888352, 374144419183933736414135771130010210994987206180928] ![(.leaf 0 (Common.fact 342).pointIds 342), (.leaf 1 (Common.fact 343).pointIds 343), (.leaf 2 (Common.fact 344).pointIds 344), (.leaf 3 (Common.fact 345).pointIds 345), Tip0141_0147, B0165, (.leaf 0 [] 0)]
theorem treeEq0146 : B0146.tree = HexagonCover.NBand.M6700_6900.SplitData.node0146 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0165
  · rfl

def B0170 : Block := .branch 171 ![63802945065326562128765061894766592385, 730750818665451459101842416358141510927477900802, 77919046967349146032132, 174224571863520570664500254341332505485320, 182687704666363189294014262516262160613012242448, 5575186299632655785383929568162090376888352, 2630702947222847842120624843358941371998678327754816] ![(.leaf 0 (Common.fact 526).pointIds 526), (.leaf 1 (Common.fact 551).pointIds 551), (.leaf 2 (Common.fact 544).pointIds 544), (.leaf 3 (Common.fact 537).pointIds 537), (.leaf 4 (Common.fact 562).pointIds 562), (.leaf 5 (Common.fact 531).pointIds 531), (.leaf 6 (Common.fact 563).pointIds 563)]
theorem treeEq0170 : B0170.tree = HexagonCover.NBand.M6700_6900.SplitData.node0170 := by
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

def B0169 : Block := .branch 170 ![63802945065326562128765061894766592385, 730750818665451459101842416358141510927477900802, 77919046967349146032132, 174224571863520570664500254341332505485320, 182687704666363189294014262516262160613012242448, 5575186299632655785383929568162090376888352, 1134125270596003253880051574657467559871003403747392] ![(.leaf 0 (Common.fact 520).pointIds 520), (.leaf 1 (Common.fact 549).pointIds 549), (.leaf 2 (Common.fact 542).pointIds 542), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 561).pointIds 561), (.leaf 5 (Common.fact 525).pointIds 525), B0170]
theorem treeEq0169 : B0169.tree = HexagonCover.NBand.M6700_6900.SplitData.node0169 := by
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
  · exact treeEq0170

def B0168 : Block := .branch 169 ![63802945065326562128765061894766592385, 730750818665451459101842416358141510927477900802, 77919046967349146032132, 174224571863520570664500254341332505485320, 182687704666363189294014262516262160613012242448, 5575186299632655785383929568162090376888352, 385836432282580959759764940306730653807165941743680] ![(.leaf 0 (Common.fact 514).pointIds 514), (.leaf 1 (Common.fact 547).pointIds 547), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 533).pointIds 533), (.leaf 4 (Common.fact 560).pointIds 560), (.leaf 5 (Common.fact 519).pointIds 519), B0169]
theorem treeEq0168 : B0168.tree = HexagonCover.NBand.M6700_6900.SplitData.node0168 := by
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
  · exact treeEq0169

def B0145 : Block := .branch 163 ![63802945065326562128765061894766592385, 730750818665451459101842416358141510927477900802, 77919046967349146032132, 174224571863520570664500254341332505485320, 182687704666363189294014262516262160613012242448, 5575186299632655785383929568162090376888352, 374144419183933736414135771130010210994987206180928] ![(.leaf 0 (Common.fact 227).pointIds 227), (.leaf 1 (Common.fact 228).pointIds 228), (.leaf 2 (Common.fact 229).pointIds 229), (.leaf 3 (Common.fact 230).pointIds 230), B0146, (.leaf 5 (Common.fact 231).pointIds 231), B0168]
theorem treeEq0145 : B0145.tree = HexagonCover.NBand.M6700_6900.SplitData.node0145 := by
  change Tree.branch (163 : Fin 175) _ = Tree.branch (163 : Fin 175) _
  apply congrArg (Tree.branch (163 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0146
  · rfl
  · exact treeEq0168

def B0171 : Block := .branch 171 ![63808136095772436767449571169291731329, 730750818665451459101842416358141510927477900802, 77919046967349146032132, 174224571863520570664500254341332505485320, 182687704666363189294014262516262160613012242448, 5575186299632655785383929568162090376888352, 374144419183933736415403421730238440396483909386304] ![(.leaf 0 (Common.fact 564).pointIds 564), (.leaf 1 (Common.fact 551).pointIds 551), (.leaf 2 (Common.fact 544).pointIds 544), (.leaf 3 (Common.fact 537).pointIds 537), (.leaf 4 (Common.fact 562).pointIds 562), (.leaf 5 (Common.fact 531).pointIds 531), (.leaf 6 (Common.fact 565).pointIds 565)]
theorem treeEq0171 : B0171.tree = HexagonCover.NBand.M6700_6900.SplitData.node0171 := by
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

def B0144 : Block := .branch 100 ![63808136095772436767449571169291731329, 730750818665451459101842416358141510927477900802, 77919046967349146032132, 174224571863520570664500254341332505485320, 182687704666363189294014262516262160613012242448, 5575186299632655785383929568162090376888352, 374144419183933736414135771130010210994987206180928] ![B0145, (.leaf 1 (Common.fact 509).pointIds 509), (.leaf 2 (Common.fact 510).pointIds 510), (.leaf 3 (Common.fact 511).pointIds 511), (.leaf 4 (Common.fact 512).pointIds 512), (.leaf 5 (Common.fact 513).pointIds 513), B0171]
theorem treeEq0144 : B0144.tree = HexagonCover.NBand.M6700_6900.SplitData.node0144 := by
  change Tree.branch (100 : Fin 175) _ = Tree.branch (100 : Fin 175) _
  apply congrArg (Tree.branch (100 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0145
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0171

def B0172 : Block := .branch 171 ![63808136095772436767449571169291731329, 618970019642691236961191426, 77919046967349146032132, 174224571863520570664500254341332505485320, 182687704666363189294014262516262160613012242448, 5575186299632655785383929568162090376888352, 374875170002599187873237613546368352504815172452416] ![(.leaf 0 (Common.fact 564).pointIds 564), (.leaf 1 (Common.fact 566).pointIds 566), (.leaf 2 (Common.fact 544).pointIds 544), (.leaf 3 (Common.fact 537).pointIds 537), (.leaf 4 (Common.fact 562).pointIds 562), (.leaf 5 (Common.fact 531).pointIds 531), (.leaf 6 (Common.fact 567).pointIds 567)]
theorem treeEq0172 : B0172.tree = HexagonCover.NBand.M6700_6900.SplitData.node0172 := by
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

def B0143 : Block := .branch 159 ![63808136095772436767449571169291731329, 618970019642691236961191426, 77919046967349146032132, 174224571863520570664500254341332505485320, 182687704666363189294014262516262160613012242448, 5575186299632655785383929568162090376888352, 374144419183933736414135771130010210994987206180928] ![(.leaf 0 (Common.fact 504).pointIds 504), B0144, (.leaf 2 (Common.fact 505).pointIds 505), (.leaf 3 (Common.fact 506).pointIds 506), (.leaf 4 (Common.fact 507).pointIds 507), (.leaf 5 (Common.fact 508).pointIds 508), B0172]
theorem treeEq0143 : B0143.tree = HexagonCover.NBand.M6700_6900.SplitData.node0143 := by
  change Tree.branch (159 : Fin 175) _ = Tree.branch (159 : Fin 175) _
  apply congrArg (Tree.branch (159 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0144
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0172

def B0175 : Block := .branch 171 ![63808136095772436767449571169291731329, 618970019642691236961191426, 77919046967349146032132, 174224571863520570664500254341332505485320, 1427247692706284399611944396176278292403421200, 182693279852662497431245988019103539547368456224, 2619010934124200618774995364697211107841430867411008] ![(.leaf 0 (Common.fact 564).pointIds 564), (.leaf 1 (Common.fact 566).pointIds 566), (.leaf 2 (Common.fact 544).pointIds 544), (.leaf 3 (Common.fact 537).pointIds 537), (.leaf 4 (Common.fact 576).pointIds 576), (.leaf 5 (Common.fact 577).pointIds 577), (.leaf 6 (Common.fact 532).pointIds 532)]
theorem treeEq0175 : B0175.tree = HexagonCover.NBand.M6700_6900.SplitData.node0175 := by
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

def B0174 : Block := .branch 170 ![63808136095772436767449571169291731329, 618970019642691236961191426, 77919046967349146032132, 174224571863520570664500254341332505485320, 1427247692706284399611944396176278292403421200, 182693279852662497431245988019103539547368456224, 1122433257497356030534422095995737295713755943403584] ![(.leaf 0 (Common.fact 572).pointIds 572), (.leaf 1 (Common.fact 573).pointIds 573), (.leaf 2 (Common.fact 542).pointIds 542), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 574).pointIds 574), (.leaf 5 (Common.fact 575).pointIds 575), B0175]
theorem treeEq0174 : B0174.tree = HexagonCover.NBand.M6700_6900.SplitData.node0174 := by
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
  · exact treeEq0175

def B0173 : Block := .branch 169 ![63808136095772436767449571169291731329, 618970019642691236961191426, 77919046967349146032132, 174224571863520570664500254341332505485320, 1427247692706284399611944396176278292403421200, 182693279852662497431245988019103539547368456224, 374144419183933736414135461645000389649918481399872] ![(.leaf 0 (Common.fact 568).pointIds 568), (.leaf 1 (Common.fact 569).pointIds 569), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 533).pointIds 533), (.leaf 4 (Common.fact 570).pointIds 570), (.leaf 5 (Common.fact 571).pointIds 571), B0174]
theorem treeEq0173 : B0173.tree = HexagonCover.NBand.M6700_6900.SplitData.node0173 := by
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
  · exact treeEq0174

def B0142 : Block := .branch 157 ![63808136095772436767449571169291731329, 618970019642691236961191426, 77919046967349146032132, 174224571863520570664500254341332505485320, 1427247692706284399611944396176278292403421200, 5575186299632655785383929568162090376888352, 374144419183933736414135771130010210994987206180928] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), B0143, B0173, (.leaf 0 [] 0)]
theorem treeEq0142 : B0142.tree = HexagonCover.NBand.M6700_6900.SplitData.node0142 := by
  change Tree.branch (157 : Fin 175) _ = Tree.branch (157 : Fin 175) _
  apply congrArg (Tree.branch (157 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0143
  · exact treeEq0173
  · rfl

def B0178 : Block := .branch 171 ![63808136095772436767449571169291731329, 618970019642691236961191426, 77919046967349146032132, 174224571863520570664500254341332505485320, 2787593150140846446350391510864201208922128, 1432822879005592536843669899017657226759634976, 2619010934124200618774995364697211107841430867411008] ![(.leaf 0 (Common.fact 564).pointIds 564), (.leaf 1 (Common.fact 566).pointIds 566), (.leaf 2 (Common.fact 544).pointIds 544), (.leaf 3 (Common.fact 537).pointIds 537), (.leaf 4 (Common.fact 582).pointIds 582), (.leaf 5 (Common.fact 583).pointIds 583), (.leaf 6 (Common.fact 532).pointIds 532)]
theorem treeEq0178 : B0178.tree = HexagonCover.NBand.M6700_6900.SplitData.node0178 := by
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

def B0177 : Block := .branch 170 ![63808136095772436767449571169291731329, 618970019642691236961191426, 77919046967349146032132, 174224571863520570664500254341332505485320, 2787593150140846446350391510864201208922128, 1432822879005592536843669899017657226759634976, 1122433257497356030534422095995737295713755943403584] ![(.leaf 0 (Common.fact 572).pointIds 572), (.leaf 1 (Common.fact 573).pointIds 573), (.leaf 2 (Common.fact 542).pointIds 542), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 580).pointIds 580), (.leaf 5 (Common.fact 581).pointIds 581), B0178]
theorem treeEq0177 : B0177.tree = HexagonCover.NBand.M6700_6900.SplitData.node0177 := by
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
  · exact treeEq0178

def B0176 : Block := .branch 169 ![63808136095772436767449571169291731329, 618970019642691236961191426, 77919046967349146032132, 174224571863520570664500254341332505485320, 2787593150140846446350391510864201208922128, 1432822879005592536843669899017657226759634976, 374144419183933736414135461645000389649918481399872] ![(.leaf 0 (Common.fact 568).pointIds 568), (.leaf 1 (Common.fact 569).pointIds 569), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 533).pointIds 533), (.leaf 4 (Common.fact 578).pointIds 578), (.leaf 5 (Common.fact 579).pointIds 579), B0177]
theorem treeEq0176 : B0176.tree = HexagonCover.NBand.M6700_6900.SplitData.node0176 := by
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
  · exact treeEq0177

def B0141 : Block := .branch 150 ![63808136095772436767449571169291731329, 618970019642691236961191426, 77919046967349146032132, 174224571863520570664500254341332505485320, 2787593150140846446350391510864201208922128, 5575186299632655785383929568162090376888352, 374144419183933736414135771130010210994987206180928] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), B0142, B0176, (.leaf 6 (Common.fact 192).pointIds 192)]
theorem treeEq0141 : B0141.tree = HexagonCover.NBand.M6700_6900.SplitData.node0141 := by
  change Tree.branch (150 : Fin 175) _ = Tree.branch (150 : Fin 175) _
  apply congrArg (Tree.branch (150 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0142
  · exact treeEq0176
  · rfl

theorem accepted0141 : B0141.accepted = true := by decide +kernel
theorem checked0141 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6700_6900.SplitData.node0141 (maskNeeds ![63808136095772436767449571169291731329, 618970019642691236961191426, 77919046967349146032132, 174224571863520570664500254341332505485320, 2787593150140846446350391510864201208922128, 5575186299632655785383929568162090376888352, 374144419183933736414135771130010210994987206180928]) := by
  rw [← treeEq0141]
  exact B0141.sound accepted0141
#print axioms checked0141

def Tip0137_0141 : Block := .tip HexagonCover.NBand.M6700_6900.SplitData.node0141 ![63808136095772436767449571169291731329, 618970019642691236961191426, 77919046967349146032132, 174224571863520570664500254341332505485320, 2787593150140846446350391510864201208922128, 5575186299632655785383929568162090376888352, 374144419183933736414135771130010210994987206180928] checked0141
def B0181 : Block := .branch 170 ![63802945065326562128765061894766592385, 730750818665451459101842416358141510927477900802, 77919046967349146032132, 174224571863520570664500254341332505485320, 2787593150140846446350391510864201208922128, 2854538941554885642239895250848741539096952864, 374144424753675518176056541098525785438169291292736] ![(.leaf 0 (Common.fact 520).pointIds 520), (.leaf 1 (Common.fact 549).pointIds 549), (.leaf 2 (Common.fact 542).pointIds 542), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 580).pointIds 580), (.leaf 5 (Common.fact 586).pointIds 586), (.leaf 6 (Common.fact 587).pointIds 587)]
theorem treeEq0181 : B0181.tree = HexagonCover.NBand.M6700_6900.SplitData.node0181 := by
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

def B0180 : Block := .branch 100 ![63802943797675961900535660398063387009, 730750818665451459101842416358141510927477900802, 77919046967349146032132, 174224571863520570664500254341332505485320, 2787593150140846446350391510864201208922128, 2854538941554885642239895250848741539096952864, 374144424753675518176056541098525785438169291292736] ![B0181, (.leaf 1 (Common.fact 509).pointIds 509), (.leaf 2 (Common.fact 510).pointIds 510), (.leaf 3 (Common.fact 511).pointIds 511), (.leaf 4 (Common.fact 512).pointIds 512), (.leaf 5 (Common.fact 513).pointIds 513), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq0180 : B0180.tree = HexagonCover.NBand.M6700_6900.SplitData.node0180 := by
  change Tree.branch (100 : Fin 175) _ = Tree.branch (100 : Fin 175) _
  apply congrArg (Tree.branch (100 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0181
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0179 : Block := .branch 159 ![63808136095772436767449571169291731329, 1099511629314, 77919046967349146032132, 174224571863520570664500254341332505485320, 2787593150140846446350391510864201208922128, 2854538941554885642239895250848741539096952864, 374144424753675518176056541098525785438169291292736] ![(.leaf 0 (Common.fact 504).pointIds 504), B0180, (.leaf 2 (Common.fact 505).pointIds 505), (.leaf 3 (Common.fact 506).pointIds 506), (.leaf 4 (Common.fact 507).pointIds 507), (.leaf 5 (Common.fact 508).pointIds 508), (.leaf 6 (Common.fact 584).pointIds 584)]
theorem treeEq0179 : B0179.tree = HexagonCover.NBand.M6700_6900.SplitData.node0179 := by
  change Tree.branch (159 : Fin 175) _ = Tree.branch (159 : Fin 175) _
  apply congrArg (Tree.branch (159 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0180
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0140 : Block := .branch 142 ![63808136095772436767449571169291731329, 618970019642691236961191426, 77919046967349146032132, 174224571863520570664500254341332505485320, 2787593150140846446350391510864201208922128, 2854538941554885642239895250848741539096952864, 374144419183933736414135771130010210994987206180928] ![(.leaf 0 (Common.fact 495).pointIds 495), (.leaf 1 (Common.fact 496).pointIds 496), (.leaf 2 (Common.fact 497).pointIds 497), (.leaf 3 (Common.fact 498).pointIds 498), (.leaf 4 (Common.fact 499).pointIds 499), Tip0137_0141, B0179]
theorem treeEq0140 : B0140.tree = HexagonCover.NBand.M6700_6900.SplitData.node0140 := by
  change Tree.branch (142 : Fin 175) _ = Tree.branch (142 : Fin 175) _
  apply congrArg (Tree.branch (142 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0179

def B0184 : Block := .branch 170 ![63802945065326562128765061894766592385, 730750818665451459101842416358141510927477900802, 77919046967349146032132, 174224571863520570664500254341332505485320, 2722259259886061366133723642610166366224, 2854538941554885642239895250848741539096952864, 374144421966082368359728648406561001357124103045184] ![(.leaf 0 (Common.fact 520).pointIds 520), (.leaf 1 (Common.fact 549).pointIds 549), (.leaf 2 (Common.fact 542).pointIds 542), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 586).pointIds 586), (.leaf 6 (Common.fact 591).pointIds 591)]
theorem treeEq0184 : B0184.tree = HexagonCover.NBand.M6700_6900.SplitData.node0184 := by
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

def B0183 : Block := .branch 100 ![63802943797675961900535660398063387009, 730750818665451459101842416358141510927477900802, 77919046967349146032132, 174224571863520570664500254341332505485320, 2722259259886061366133723642610166366224, 2854538941554885642239895250848741539096952864, 374144421966082368359728648406561001357124103045184] ![B0184, (.leaf 1 (Common.fact 509).pointIds 509), (.leaf 2 (Common.fact 510).pointIds 510), (.leaf 3 (Common.fact 511).pointIds 511), (.leaf 4 (Common.fact 512).pointIds 512), (.leaf 5 (Common.fact 513).pointIds 513), (.leaf 6 (Common.fact 589).pointIds 589)]
theorem treeEq0183 : B0183.tree = HexagonCover.NBand.M6700_6900.SplitData.node0183 := by
  change Tree.branch (100 : Fin 175) _ = Tree.branch (100 : Fin 175) _
  apply congrArg (Tree.branch (100 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0184
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0182 : Block := .branch 159 ![63808136095772436767449571169291731329, 1099511629314, 77919046967349146032132, 174224571863520570664500254341332505485320, 2722259259886061366133723642610166366224, 2854538941554885642239895250848741539096952864, 374144421966082368359728648406561001357124103045184] ![(.leaf 0 (Common.fact 504).pointIds 504), B0183, (.leaf 2 (Common.fact 505).pointIds 505), (.leaf 3 (Common.fact 506).pointIds 506), (.leaf 4 (Common.fact 507).pointIds 507), (.leaf 5 (Common.fact 508).pointIds 508), (.leaf 6 (Common.fact 588).pointIds 588)]
theorem treeEq0182 : B0182.tree = HexagonCover.NBand.M6700_6900.SplitData.node0182 := by
  change Tree.branch (159 : Fin 175) _ = Tree.branch (159 : Fin 175) _
  apply congrArg (Tree.branch (159 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0183
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0139 : Block := .branch 141 ![63808136095772436767449571169291731329, 618970019642691236961191426, 77919046967349146032132, 174224571863520570664500254341332505485320, 2722259259886061366133723642610166366224, 2854538941554885642239895250848741539096952864, 374144419183933736414135771130010210994987206180928] ![(.leaf 0 (Common.fact 110).pointIds 110), (.leaf 1 (Common.fact 111).pointIds 111), (.leaf 2 (Common.fact 112).pointIds 112), (.leaf 3 (Common.fact 113).pointIds 113), B0140, (.leaf 5 (Common.fact 114).pointIds 114), B0182]
theorem treeEq0139 : B0139.tree = HexagonCover.NBand.M6700_6900.SplitData.node0139 := by
  change Tree.branch (141 : Fin 175) _ = Tree.branch (141 : Fin 175) _
  apply congrArg (Tree.branch (141 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0140
  · rfl
  · exact treeEq0182

def B0188 : Block := .branch 171 ![63808136095772436767449571169291731329, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 176946831123406554659381522647675490631696, 233843116511886021798231813129856131886488303829024, 1870722095810778324654708730346474201777593405407296] ![(.leaf 0 (Common.fact 564).pointIds 564), (.leaf 1 (Common.fact 566).pointIds 566), (.leaf 2 (Common.fact 544).pointIds 544), (.leaf 3 (Common.fact 597).pointIds 597), (.leaf 4 (Common.fact 598).pointIds 598), (.leaf 5 (Common.fact 599).pointIds 599), (.leaf 6 (Common.fact 600).pointIds 600)]
theorem treeEq0188 : B0188.tree = HexagonCover.NBand.M6700_6900.SplitData.node0188 := by
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

def B0187 : Block := .branch 170 ![63808136095772436767449571169291731329, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 176946831123406554659381522647675490631696, 233843116511886021798231813129856131886488303829024, 374144419183933736414135461645000389649918481399872] ![(.leaf 0 (Common.fact 572).pointIds 572), (.leaf 1 (Common.fact 573).pointIds 573), (.leaf 2 (Common.fact 542).pointIds 542), (.leaf 3 (Common.fact 594).pointIds 594), (.leaf 4 (Common.fact 595).pointIds 595), (.leaf 5 (Common.fact 596).pointIds 596), B0188]
theorem treeEq0187 : B0187.tree = HexagonCover.NBand.M6700_6900.SplitData.node0187 := by
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
  · exact treeEq0188

def B0186 : Block := .branch 165 ![63808136095772436767449571169291731329, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 176946831123406554659381522647675490631696, 187075064117297128415713898482935075257498462453792, 374144419183933736414135461645000389649918481399872] ![(.leaf 0 (Common.fact 342).pointIds 342), (.leaf 1 (Common.fact 343).pointIds 343), (.leaf 2 (Common.fact 344).pointIds 344), (.leaf 3 (Common.fact 345).pointIds 345), (.leaf 4 (Common.fact 593).pointIds 593), B0187, (.leaf 0 [] 0)]
theorem treeEq0186 : B0186.tree = HexagonCover.NBand.M6700_6900.SplitData.node0186 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0187
  · rfl

def B0185 : Block := .branch 167 ![63808136095772436767449571169291731329, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 176946831123406554659381522647675490631696, 2854538941554885642239895250848741539096952864, 374144419183933736414135461645000389649918481399872] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 339).pointIds 339), (.leaf 4 (Common.fact 592).pointIds 592), B0186, (.leaf 6 (Common.fact 341).pointIds 341)]
theorem treeEq0185 : B0185.tree = HexagonCover.NBand.M6700_6900.SplitData.node0185 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0186
  · rfl

def B0138 : Block := .branch 137 ![63808136095772436767449571169291731329, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 2722259259886061366133723642610166366224, 2854538941554885642239895250848741539096952864, 374144419183933736414135771130010210994987206180928] ![(.leaf 0 (Common.fact 239).pointIds 239), (.leaf 1 (Common.fact 240).pointIds 240), (.leaf 2 (Common.fact 241).pointIds 241), B0139, B0185, (.leaf 5 (Common.fact 243).pointIds 243), (.leaf 0 [] 0)]
theorem treeEq0138 : B0138.tree = HexagonCover.NBand.M6700_6900.SplitData.node0138 := by
  change Tree.branch (137 : Fin 175) _ = Tree.branch (137 : Fin 175) _
  apply congrArg (Tree.branch (137 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0139
  · exact treeEq0185
  · rfl
  · rfl

def B0193 : Block := .branch 171 ![63808136095772436767449571169291731329, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 2787593150140846446350391510864201208922128, 5575186299632655785383929568162090376888352, 1870722095854334467620588853669786151528859736473664] ![(.leaf 0 (Common.fact 564).pointIds 564), (.leaf 1 (Common.fact 566).pointIds 566), (.leaf 2 (Common.fact 544).pointIds 544), (.leaf 3 (Common.fact 597).pointIds 597), (.leaf 4 (Common.fact 582).pointIds 582), (.leaf 5 (Common.fact 531).pointIds 531), (.leaf 6 (Common.fact 609).pointIds 609)]
theorem treeEq0193 : B0193.tree = HexagonCover.NBand.M6700_6900.SplitData.node0193 := by
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

def B0192 : Block := .branch 170 ![63808136095772436767449571169291731329, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 2787593150140846446350391510864201208922128, 5575186299632655785383929568162090376888352, 374144419227489879380015584968312339401184812466240] ![(.leaf 0 (Common.fact 572).pointIds 572), (.leaf 1 (Common.fact 573).pointIds 573), (.leaf 2 (Common.fact 542).pointIds 542), (.leaf 3 (Common.fact 594).pointIds 594), (.leaf 4 (Common.fact 580).pointIds 580), (.leaf 5 (Common.fact 525).pointIds 525), B0193]
theorem treeEq0192 : B0192.tree = HexagonCover.NBand.M6700_6900.SplitData.node0192 := by
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
  · exact treeEq0193

def B0191 : Block := .branch 141 ![63808136095772436767449571169291731329, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 5575186299632655785383929568162090376888352, 374144419227489879380015894453322160746253537247296] ![(.leaf 0 (Common.fact 110).pointIds 110), (.leaf 1 (Common.fact 111).pointIds 111), (.leaf 2 (Common.fact 112).pointIds 112), (.leaf 3 (Common.fact 113).pointIds 113), B0192, (.leaf 5 (Common.fact 114).pointIds 114), (.leaf 6 (Common.fact 608).pointIds 608)]
theorem treeEq0191 : B0191.tree = HexagonCover.NBand.M6700_6900.SplitData.node0191 := by
  change Tree.branch (141 : Fin 175) _ = Tree.branch (141 : Fin 175) _
  apply congrArg (Tree.branch (141 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0192
  · rfl
  · rfl

def B0190 : Block := .branch 142 ![63808136095772436767449571169291731329, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 393248, 374144419227489879380015894453322160746253537247296] ![(.leaf 0 (Common.fact 495).pointIds 495), (.leaf 1 (Common.fact 496).pointIds 496), (.leaf 2 (Common.fact 497).pointIds 497), (.leaf 3 (Common.fact 498).pointIds 498), (.leaf 4 (Common.fact 499).pointIds 499), B0191, (.leaf 6 (Common.fact 607).pointIds 607)]
theorem treeEq0190 : B0190.tree = HexagonCover.NBand.M6700_6900.SplitData.node0190 := by
  change Tree.branch (142 : Fin 175) _ = Tree.branch (142 : Fin 175) _
  apply congrArg (Tree.branch (142 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0191
  · rfl

def B0189 : Block := .branch 143 ![63808136095772436767449571169291731329, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 393248, 374144419227489879380015894453322160746253537247296] ![(.leaf 0 (Common.fact 601).pointIds 601), (.leaf 1 (Common.fact 602).pointIds 602), (.leaf 2 (Common.fact 603).pointIds 603), (.leaf 3 (Common.fact 604).pointIds 604), (.leaf 4 (Common.fact 605).pointIds 605), B0190, (.leaf 6 (Common.fact 606).pointIds 606)]
theorem treeEq0189 : B0189.tree = HexagonCover.NBand.M6700_6900.SplitData.node0189 := by
  change Tree.branch (143 : Fin 175) _ = Tree.branch (143 : Fin 175) _
  apply congrArg (Tree.branch (143 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0190
  · rfl

def B0137 : Block := .branch 135 ![63808136095772436767449571169291731329, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 2722259259886061366133723642610166366224, 2854495385411919762116571938898990272765886496, 374144419183933736414135771130010210994987206180928] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), (.leaf 4 (Common.fact 150).pointIds 150), B0138, B0189]
theorem treeEq0137 : B0137.tree = HexagonCover.NBand.M6700_6900.SplitData.node0137 := by
  change Tree.branch (135 : Fin 175) _ = Tree.branch (135 : Fin 175) _
  apply congrArg (Tree.branch (135 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0138
  · exact treeEq0189

theorem accepted0137 : B0137.accepted = true := by decide +kernel
theorem checked0137 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6700_6900.SplitData.node0137 (maskNeeds ![63808136095772436767449571169291731329, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 2722259259886061366133723642610166366224, 2854495385411919762116571938898990272765886496, 374144419183933736414135771130010210994987206180928]) := by
  rw [← treeEq0137]
  exact B0137.sound accepted0137
#print axioms checked0137

def Tip0134_0137 : Block := .tip HexagonCover.NBand.M6700_6900.SplitData.node0137 ![63808136095772436767449571169291731329, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 2722259259886061366133723642610166366224, 2854495385411919762116571938898990272765886496, 374144419183933736414135771130010210994987206180928] checked0137
def B0195 : Block := .branch 171 ![63808136095772436767449571169291731329, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 1329552514338574299630590216301019152, 2854495385411919762116571938898990272765886496, 1870722095813500583590076238054181198637047551098944] ![(.leaf 0 (Common.fact 564).pointIds 564), (.leaf 1 (Common.fact 566).pointIds 566), (.leaf 2 (Common.fact 544).pointIds 544), (.leaf 3 (Common.fact 597).pointIds 597), (.leaf 4 (Common.fact 612).pointIds 612), (.leaf 5 (Common.fact 613).pointIds 613), (.leaf 6 (Common.fact 614).pointIds 614)]
theorem treeEq0195 : B0195.tree = HexagonCover.NBand.M6700_6900.SplitData.node0195 := by
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

def B0194 : Block := .branch 170 ![63808136095772436767449571169291731329, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 1329552514338574299630590216301019152, 2854495385411919762116571938898990272765886496, 374144419186655995349502969352707386509372627091520] ![(.leaf 0 (Common.fact 572).pointIds 572), (.leaf 1 (Common.fact 573).pointIds 573), (.leaf 2 (Common.fact 542).pointIds 542), (.leaf 3 (Common.fact 594).pointIds 594), (.leaf 4 (Common.fact 610).pointIds 610), (.leaf 5 (Common.fact 611).pointIds 611), B0195]
theorem treeEq0194 : B0194.tree = HexagonCover.NBand.M6700_6900.SplitData.node0194 := by
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
  · exact treeEq0195

def B0136 : Block := .branch 131 ![63808136095772436767449571169291731329, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 1329552514338574299630590216301019152, 2854495385411919762116571938898990272765886496, 374144419183933736414135771130010210994987206180928] ![(.leaf 0 (Common.fact 490).pointIds 490), (.leaf 1 (Common.fact 491).pointIds 491), (.leaf 2 (Common.fact 492).pointIds 492), (.leaf 3 (Common.fact 493).pointIds 493), Tip0134_0137, (.leaf 5 (Common.fact 494).pointIds 494), B0194]
theorem treeEq0136 : B0136.tree = HexagonCover.NBand.M6700_6900.SplitData.node0136 := by
  change Tree.branch (131 : Fin 175) _ = Tree.branch (131 : Fin 175) _
  apply congrArg (Tree.branch (131 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0194

def B0201 : Block := .branch 170 ![21267649200209254195843235965795565953, 730750818665451459101842416358141510927477900802, 77919046967349146032132, 77371252455336267181219848, 1427247692706284399611944396176278292403421200, 2854495427947215627233879871820816201736912928, 374144435904048117441368111866384921762350044282944] ![(.leaf 0 (Common.fact 620).pointIds 620), (.leaf 1 (Common.fact 549).pointIds 549), (.leaf 2 (Common.fact 542).pointIds 542), (.leaf 3 (Common.fact 594).pointIds 594), (.leaf 4 (Common.fact 574).pointIds 574), (.leaf 5 (Common.fact 621).pointIds 621), (.leaf 6 (Common.fact 622).pointIds 622)]
theorem treeEq0201 : B0201.tree = HexagonCover.NBand.M6700_6900.SplitData.node0201 := by
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

def B0200 : Block := .branch 142 ![21267649200209254195843235965795565953, 730750818665451459101842416358141510927477900802, 77919046967349146032132, 77371252455336267181219848, 1427247692706284399611944396176278292403421200, 2854495427947215627233879871820816201736912928, 374144430328861817808712326482455353600259667787840] ![(.leaf 0 (Common.fact 495).pointIds 495), (.leaf 1 (Common.fact 496).pointIds 496), (.leaf 2 (Common.fact 497).pointIds 497), (.leaf 3 (Common.fact 498).pointIds 498), (.leaf 4 (Common.fact 499).pointIds 499), (.leaf 5 (Common.fact 619).pointIds 619), B0201]
theorem treeEq0200 : B0200.tree = HexagonCover.NBand.M6700_6900.SplitData.node0200 := by
  change Tree.branch (142 : Fin 175) _ = Tree.branch (142 : Fin 175) _
  apply congrArg (Tree.branch (142 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0201

def B0199 : Block := .branch 100 ![21267647932558653967613834469092360577, 730750818665451459101842416358141510927477900802, 77919046967349146032132, 77371252455336267181219848, 1427247692706284399611944396176278292403421200, 2854495427947215627233879871820816201736912928, 374144430334306335679447341897869347319167959171136] ![B0200, (.leaf 1 (Common.fact 509).pointIds 509), (.leaf 2 (Common.fact 510).pointIds 510), (.leaf 3 (Common.fact 511).pointIds 511), (.leaf 4 (Common.fact 512).pointIds 512), (.leaf 5 (Common.fact 513).pointIds 513), (.leaf 6 (Common.fact 618).pointIds 618)]
theorem treeEq0199 : B0199.tree = HexagonCover.NBand.M6700_6900.SplitData.node0199 := by
  change Tree.branch (100 : Fin 175) _ = Tree.branch (100 : Fin 175) _
  apply congrArg (Tree.branch (100 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0200
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0198 : Block := .branch 159 ![21272840230655128834527745240320704897, 1099511629314, 77919046967349146032132, 77371252455336267181219848, 1427247692706284399611944396176278292403421200, 2854495427947215627233879871820816201736912928, 374144430334306335679447341897869347319167959171136] ![(.leaf 0 (Common.fact 504).pointIds 504), B0199, (.leaf 2 (Common.fact 505).pointIds 505), (.leaf 3 (Common.fact 506).pointIds 506), (.leaf 4 (Common.fact 507).pointIds 507), (.leaf 5 (Common.fact 508).pointIds 508), (.leaf 6 (Common.fact 617).pointIds 617)]
theorem treeEq0198 : B0198.tree = HexagonCover.NBand.M6700_6900.SplitData.node0198 := by
  change Tree.branch (159 : Fin 175) _ = Tree.branch (159 : Fin 175) _
  apply congrArg (Tree.branch (159 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0199
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0197 : Block := .branch 143 ![21272840230655128834527745240320704897, 1099511629314, 77919046967349146032132, 77371252455336267181219848, 1427247692706284399611944396176278292403421200, 2854495427947215627233879871820816201736912928, 374144419183933736414135771130010210994987206180928] ![(.leaf 0 (Common.fact 601).pointIds 601), (.leaf 1 (Common.fact 602).pointIds 602), (.leaf 2 (Common.fact 603).pointIds 603), (.leaf 3 (Common.fact 604).pointIds 604), (.leaf 4 (Common.fact 605).pointIds 605), (.leaf 5 (Common.fact 616).pointIds 616), B0198]
theorem treeEq0197 : B0197.tree = HexagonCover.NBand.M6700_6900.SplitData.node0197 := by
  change Tree.branch (143 : Fin 175) _ = Tree.branch (143 : Fin 175) _
  apply congrArg (Tree.branch (143 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0198

def B0196 : Block := .branch 150 ![21272840230655128834527745240320704897, 1099511629314, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 2854495427947215627233879871820816201736912928, 374144419183933736414135771130010210994987206180928] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), B0197, (.leaf 5 (Common.fact 615).pointIds 615), (.leaf 6 (Common.fact 192).pointIds 192)]
theorem treeEq0196 : B0196.tree = HexagonCover.NBand.M6700_6900.SplitData.node0196 := by
  change Tree.branch (150 : Fin 175) _ = Tree.branch (150 : Fin 175) _
  apply congrArg (Tree.branch (150 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0197
  · rfl
  · rfl

def B0135 : Block := .branch 125 ![21272840230655128834527745240320704897, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 1329552514338574299630590216301019152, 2854495385411919762116571938898990272765886496, 374144419183933736414135771130010210994987206180928] ![B0136, (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), B0196, (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq0135 : B0135.tree = HexagonCover.NBand.M6700_6900.SplitData.node0135 := by
  change Tree.branch (125 : Fin 175) _ = Tree.branch (125 : Fin 175) _
  apply congrArg (Tree.branch (125 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0136
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0196
  · rfl

def B0208 : Block := .branch 171 ![42540488163213782800988658204806218113, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 2787593150140846446350391510864201208922128, 5575186299632655785383929568162090376888352, 2619010934124221886422927923351177568754395352924224] ![(.leaf 0 (Common.fact 629).pointIds 629), (.leaf 1 (Common.fact 566).pointIds 566), (.leaf 2 (Common.fact 544).pointIds 544), (.leaf 3 (Common.fact 597).pointIds 597), (.leaf 4 (Common.fact 582).pointIds 582), (.leaf 5 (Common.fact 531).pointIds 531), (.leaf 6 (Common.fact 630).pointIds 630)]
theorem treeEq0208 : B0208.tree = HexagonCover.NBand.M6700_6900.SplitData.node0208 := by
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

def B0207 : Block := .branch 170 ![42540488163213782800988658204806218113, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 2787593150140846446350391510864201208922128, 5575186299632655785383929568162090376888352, 1122433257497377298182354654649703756626720428916800] ![(.leaf 0 (Common.fact 628).pointIds 628), (.leaf 1 (Common.fact 573).pointIds 573), (.leaf 2 (Common.fact 542).pointIds 542), (.leaf 3 (Common.fact 594).pointIds 594), (.leaf 4 (Common.fact 580).pointIds 580), (.leaf 5 (Common.fact 525).pointIds 525), B0208]
theorem treeEq0207 : B0207.tree = HexagonCover.NBand.M6700_6900.SplitData.node0207 := by
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
  · exact treeEq0208

def B0206 : Block := .branch 169 ![42540488163213782800988658204806218113, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 2787593150140846446350391510864201208922128, 5575186299632655785383929568162090376888352, 374144419183955004062068020298966850562882966913088] ![(.leaf 0 (Common.fact 626).pointIds 626), (.leaf 1 (Common.fact 569).pointIds 569), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 627).pointIds 627), (.leaf 4 (Common.fact 578).pointIds 578), (.leaf 5 (Common.fact 519).pointIds 519), B0207]
theorem treeEq0206 : B0206.tree = HexagonCover.NBand.M6700_6900.SplitData.node0206 := by
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
  · exact treeEq0207

def B0205 : Block := .branch 141 ![42540488163213782800988658204806218113, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 5575186299632655785383929568162090376888352, 374144419183955004062068329783976671907951691694144] ![(.leaf 0 (Common.fact 110).pointIds 110), (.leaf 1 (Common.fact 111).pointIds 111), (.leaf 2 (Common.fact 112).pointIds 112), (.leaf 3 (Common.fact 113).pointIds 113), B0206, (.leaf 5 (Common.fact 114).pointIds 114), (.leaf 6 (Common.fact 625).pointIds 625)]
theorem treeEq0205 : B0205.tree = HexagonCover.NBand.M6700_6900.SplitData.node0205 := by
  change Tree.branch (141 : Fin 175) _ = Tree.branch (141 : Fin 175) _
  apply congrArg (Tree.branch (141 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0206
  · rfl
  · rfl

def B0204 : Block := .branch 142 ![42540488163213782800988658204806218113, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 393248, 374144419183955004062068329783976671907951691694144] ![(.leaf 0 (Common.fact 495).pointIds 495), (.leaf 1 (Common.fact 496).pointIds 496), (.leaf 2 (Common.fact 497).pointIds 497), (.leaf 3 (Common.fact 498).pointIds 498), (.leaf 4 (Common.fact 499).pointIds 499), B0205, (.leaf 6 (Common.fact 624).pointIds 624)]
theorem treeEq0204 : B0204.tree = HexagonCover.NBand.M6700_6900.SplitData.node0204 := by
  change Tree.branch (142 : Fin 175) _ = Tree.branch (142 : Fin 175) _
  apply congrArg (Tree.branch (142 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0205
  · rfl

def B0203 : Block := .branch 125 ![5192298096474868066832275835191681, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 2865645758011185073687339798035314453518876704, 374144419183955004062068329783976671907951691694144] ![B0204, (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), (.leaf 5 (Common.fact 616).pointIds 616), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq0203 : B0203.tree = HexagonCover.NBand.M6700_6900.SplitData.node0203 := by
  change Tree.branch (125 : Fin 175) _ = Tree.branch (125 : Fin 175) _
  apply congrArg (Tree.branch (125 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0204
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0202 : Block := .branch 143 ![5192298096474868066832275835191681, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 2854495385411919762116571938898990272765886496, 374144419183955004062068329783976671907951691694144] ![(.leaf 0 (Common.fact 601).pointIds 601), (.leaf 1 (Common.fact 602).pointIds 602), (.leaf 2 (Common.fact 603).pointIds 603), (.leaf 3 (Common.fact 604).pointIds 604), (.leaf 4 (Common.fact 605).pointIds 605), B0203, (.leaf 6 (Common.fact 623).pointIds 623)]
theorem treeEq0202 : B0202.tree = HexagonCover.NBand.M6700_6900.SplitData.node0202 := by
  change Tree.branch (143 : Fin 175) _ = Tree.branch (143 : Fin 175) _
  apply congrArg (Tree.branch (143 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0203
  · rfl

def B0134 : Block := .branch 124 ![5192298096474868066832275835191681, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 1329552514338574299630590216301019152, 2854495385411919762116571938898990272765886496, 374144419183933736414135771130010210994987206180928] ![B0135, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 204).pointIds 204), B0202]
theorem treeEq0134 : B0134.tree = HexagonCover.NBand.M6700_6900.SplitData.node0134 := by
  change Tree.branch (124 : Fin 175) _ = Tree.branch (124 : Fin 175) _
  apply congrArg (Tree.branch (124 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0135
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0202

theorem accepted0134 : B0134.accepted = true := by decide +kernel
theorem checked0134 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6700_6900.SplitData.node0134 (maskNeeds ![5192298096474868066832275835191681, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 1329552514338574299630590216301019152, 2854495385411919762116571938898990272765886496, 374144419183933736414135771130010210994987206180928]) := by
  rw [← treeEq0134]
  exact B0134.sound accepted0134
#print axioms checked0134

def Tip0128_0134 : Block := .tip HexagonCover.NBand.M6700_6900.SplitData.node0134 ![5192298096474868066832275835191681, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 1329552514338574299630590216301019152, 2854495385411919762116571938898990272765886496, 374144419183933736414135771130010210994987206180928] checked0134
def B0210 : Block := .branch 171 ![5192298096474868066832275835191681, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 2854495385411919762116571938898990272765886496, 1870722095810779653882704515262347105584653685751872] ![(.leaf 0 (Common.fact 633).pointIds 633), (.leaf 1 (Common.fact 566).pointIds 566), (.leaf 2 (Common.fact 544).pointIds 544), (.leaf 3 (Common.fact 597).pointIds 597), (.leaf 4 (Common.fact 634).pointIds 634), (.leaf 5 (Common.fact 613).pointIds 613), (.leaf 6 (Common.fact 635).pointIds 635)]
theorem treeEq0210 : B0210.tree = HexagonCover.NBand.M6700_6900.SplitData.node0210 := by
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

def B0209 : Block := .branch 170 ![5192298096474868066832275835191681, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 2854495385411919762116571938898990272765886496, 374144419183935065642131246560873293456978761744448] ![(.leaf 0 (Common.fact 631).pointIds 631), (.leaf 1 (Common.fact 573).pointIds 573), (.leaf 2 (Common.fact 542).pointIds 542), (.leaf 3 (Common.fact 594).pointIds 594), (.leaf 4 (Common.fact 632).pointIds 632), (.leaf 5 (Common.fact 611).pointIds 611), B0210]
theorem treeEq0209 : B0209.tree = HexagonCover.NBand.M6700_6900.SplitData.node0209 := by
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
  · exact treeEq0210

def B0133 : Block := .branch 120 ![5192298096474868066832275835191681, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 2854495385411919762116571938898990272765886496, 374144419183933736414135771130010210994987206180928] ![(.leaf 0 (Common.fact 485).pointIds 485), (.leaf 1 (Common.fact 486).pointIds 486), (.leaf 2 (Common.fact 487).pointIds 487), (.leaf 3 (Common.fact 488).pointIds 488), Tip0128_0134, (.leaf 5 (Common.fact 489).pointIds 489), B0209]
theorem treeEq0133 : B0133.tree = HexagonCover.NBand.M6700_6900.SplitData.node0133 := by
  change Tree.branch (120 : Fin 175) _ = Tree.branch (120 : Fin 175) _
  apply congrArg (Tree.branch (120 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0209

def B0216 : Block := .branch 171 ![93536104789220322060902184541815473385688159748481, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 2787593150140846446350391510864201208922128, 5575186299632655785383929568162090376888352, 374144419183933741606432629664837839525483535401024] ![(.leaf 0 (Common.fact 640).pointIds 640), (.leaf 1 (Common.fact 566).pointIds 566), (.leaf 2 (Common.fact 544).pointIds 544), (.leaf 3 (Common.fact 597).pointIds 597), (.leaf 4 (Common.fact 582).pointIds 582), (.leaf 5 (Common.fact 531).pointIds 531), (.leaf 6 (Common.fact 641).pointIds 641)]
theorem treeEq0216 : B0216.tree = HexagonCover.NBand.M6700_6900.SplitData.node0216 := by
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

def B0215 : Block := .branch 141 ![93536104789220322060902184541815473385688159748481, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 5575186299632655785383929568162090376888352, 374144419183933741606432629664837839525483535401024] ![(.leaf 0 (Common.fact 110).pointIds 110), (.leaf 1 (Common.fact 111).pointIds 111), (.leaf 2 (Common.fact 112).pointIds 112), (.leaf 3 (Common.fact 113).pointIds 113), B0216, (.leaf 5 (Common.fact 114).pointIds 114), (.leaf 6 (Common.fact 639).pointIds 639)]
theorem treeEq0215 : B0215.tree = HexagonCover.NBand.M6700_6900.SplitData.node0215 := by
  change Tree.branch (141 : Fin 175) _ = Tree.branch (141 : Fin 175) _
  apply congrArg (Tree.branch (141 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0216
  · rfl
  · rfl

def B0214 : Block := .branch 142 ![93536104789220322060902184541815473385688159748481, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 393248, 374144419183933741606432629664837839525483535401024] ![(.leaf 0 (Common.fact 495).pointIds 495), (.leaf 1 (Common.fact 496).pointIds 496), (.leaf 2 (Common.fact 497).pointIds 497), (.leaf 3 (Common.fact 498).pointIds 498), (.leaf 4 (Common.fact 499).pointIds 499), B0215, (.leaf 6 (Common.fact 638).pointIds 638)]
theorem treeEq0214 : B0214.tree = HexagonCover.NBand.M6700_6900.SplitData.node0214 := by
  change Tree.branch (142 : Fin 175) _ = Tree.branch (142 : Fin 175) _
  apply congrArg (Tree.branch (142 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0215
  · rfl

def B0213 : Block := .branch 125 ![93536104789177786765037067233882551559759188722049, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 2865645758011185073687339798035314453518876704, 374144419183933741606432629664837839525483535401024] ![B0214, (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), (.leaf 5 (Common.fact 616).pointIds 616), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq0213 : B0213.tree = HexagonCover.NBand.M6700_6900.SplitData.node0213 := by
  change Tree.branch (125 : Fin 175) _ = Tree.branch (125 : Fin 175) _
  apply congrArg (Tree.branch (125 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0214
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0212 : Block := .branch 143 ![93536104789177786765037067233882551559759188722049, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 2854495385411919762116571938898990272765886496, 374144419183933741606432629664837839525483535401024] ![(.leaf 0 (Common.fact 601).pointIds 601), (.leaf 1 (Common.fact 602).pointIds 602), (.leaf 2 (Common.fact 603).pointIds 603), (.leaf 3 (Common.fact 604).pointIds 604), (.leaf 4 (Common.fact 605).pointIds 605), B0213, (.leaf 6 (Common.fact 637).pointIds 637)]
theorem treeEq0212 : B0212.tree = HexagonCover.NBand.M6700_6900.SplitData.node0212 := by
  change Tree.branch (143 : Fin 175) _ = Tree.branch (143 : Fin 175) _
  apply congrArg (Tree.branch (143 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0213
  · rfl

def B0211 : Block := .branch 166 ![1237940040438301779505971585, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 2854495385411919762116571938898990272765886496, 374144419183933741606432629664837839525483535401024] ![B0212, (.leaf 1 (Common.fact 216).pointIds 216), (.leaf 2 (Common.fact 217).pointIds 217), (.leaf 3 (Common.fact 218).pointIds 218), (.leaf 4 (Common.fact 219).pointIds 219), (.leaf 5 (Common.fact 238).pointIds 238), (.leaf 6 (Common.fact 636).pointIds 636)]
theorem treeEq0211 : B0211.tree = HexagonCover.NBand.M6700_6900.SplitData.node0211 := by
  change Tree.branch (166 : Fin 175) _ = Tree.branch (166 : Fin 175) _
  apply congrArg (Tree.branch (166 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0212
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0132 : Block := .branch 112 ![1237940040438301779505971585, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 2854495385411919762116571938898990272765886496, 374144419183933736414135771130010210994987206180928] ![B0133, (.leaf 1 (Common.fact 210).pointIds 210), (.leaf 2 (Common.fact 211).pointIds 211), (.leaf 3 (Common.fact 212).pointIds 212), (.leaf 4 (Common.fact 213).pointIds 213), (.leaf 5 (Common.fact 214).pointIds 214), B0211]
theorem treeEq0132 : B0132.tree = HexagonCover.NBand.M6700_6900.SplitData.node0132 := by
  change Tree.branch (112 : Fin 175) _ = Tree.branch (112 : Fin 175) _
  apply congrArg (Tree.branch (112 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0133
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0211

def B0218 : Block := .branch 171 ![10387129018874575778592805259051393, 1856910058928071511860315650, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 2854495385411919762116571938898990272765886496, 1870722095810778324654708730346474201777593405407296] ![(.leaf 0 (Common.fact 644).pointIds 644), (.leaf 1 (Common.fact 645).pointIds 645), (.leaf 2 (Common.fact 544).pointIds 544), (.leaf 3 (Common.fact 597).pointIds 597), (.leaf 4 (Common.fact 634).pointIds 634), (.leaf 5 (Common.fact 613).pointIds 613), (.leaf 6 (Common.fact 600).pointIds 600)]
theorem treeEq0218 : B0218.tree = HexagonCover.NBand.M6700_6900.SplitData.node0218 := by
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

def B0217 : Block := .branch 170 ![10387129018874575778592805259051393, 1856910058928071511860315650, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 2854495385411919762116571938898990272765886496, 374144419183933736414135461645000389649918481399872] ![(.leaf 0 (Common.fact 642).pointIds 642), (.leaf 1 (Common.fact 643).pointIds 643), (.leaf 2 (Common.fact 542).pointIds 542), (.leaf 3 (Common.fact 594).pointIds 594), (.leaf 4 (Common.fact 632).pointIds 632), (.leaf 5 (Common.fact 611).pointIds 611), B0218]
theorem treeEq0217 : B0217.tree = HexagonCover.NBand.M6700_6900.SplitData.node0217 := by
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
  · exact treeEq0218

def B0131 : Block := .branch 90 ![10387129018874575778592805259051393, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 2854495385411919762116571938898990272765886496, 374144419183933736414135771130010210994987206180928] ![B0132, B0217, (.leaf 2 (Common.fact 316).pointIds 316), (.leaf 3 (Common.fact 317).pointIds 317), (.leaf 4 (Common.fact 318).pointIds 318), (.leaf 5 (Common.fact 319).pointIds 319), (.leaf 6 (Common.fact 484).pointIds 484)]
theorem treeEq0131 : B0131.tree = HexagonCover.NBand.M6700_6900.SplitData.node0131 := by
  change Tree.branch (90 : Fin 175) _ = Tree.branch (90 : Fin 175) _
  apply congrArg (Tree.branch (90 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0132
  · exact treeEq0217
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0220 : Block := .branch 171 ![10387129018270703164595849377350017, 619574482552498551548544514, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 2854495385411919762116571938898990272765886496, 1870722095810778324654708730346474201777593405407296] ![(.leaf 0 (Common.fact 648).pointIds 648), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 544).pointIds 544), (.leaf 3 (Common.fact 597).pointIds 597), (.leaf 4 (Common.fact 634).pointIds 634), (.leaf 5 (Common.fact 613).pointIds 613), (.leaf 6 (Common.fact 600).pointIds 600)]
theorem treeEq0220 : B0220.tree = HexagonCover.NBand.M6700_6900.SplitData.node0220 := by
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

def B0219 : Block := .branch 170 ![10387129018270703164595849377350017, 619574482552498551548544514, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 2854495385411919762116571938898990272765886496, 374144419183933736414135461645000389649918481399872] ![(.leaf 0 (Common.fact 646).pointIds 646), (.leaf 1 (Common.fact 647).pointIds 647), (.leaf 2 (Common.fact 542).pointIds 542), (.leaf 3 (Common.fact 594).pointIds 594), (.leaf 4 (Common.fact 632).pointIds 632), (.leaf 5 (Common.fact 611).pointIds 611), B0220]
theorem treeEq0219 : B0219.tree = HexagonCover.NBand.M6700_6900.SplitData.node0219 := by
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
  · exact treeEq0220

def B0130 : Block := .branch 79 ![10387129018270703164595849377350017, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 2854495385411919762116571938898990272765886496, 374144419183933736414135771130010210994987206180928] ![B0131, B0219, (.leaf 2 (Common.fact 305).pointIds 305), (.leaf 3 (Common.fact 306).pointIds 306), (.leaf 4 (Common.fact 307).pointIds 307), (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 483).pointIds 483)]
theorem treeEq0130 : B0130.tree = HexagonCover.NBand.M6700_6900.SplitData.node0130 := by
  change Tree.branch (79 : Fin 175) _ = Tree.branch (79 : Fin 175) _
  apply congrArg (Tree.branch (79 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0131
  · exact treeEq0219
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0222 : Block := .branch 171 ![10387129018270112868785490671698305, 618970609938501595666843138, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 2854495385411919762116571938898990272765886496, 1870722095810778324654708730346474201777593405407296] ![(.leaf 0 (Common.fact 652).pointIds 652), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 544).pointIds 544), (.leaf 3 (Common.fact 597).pointIds 597), (.leaf 4 (Common.fact 634).pointIds 634), (.leaf 5 (Common.fact 613).pointIds 613), (.leaf 6 (Common.fact 600).pointIds 600)]
theorem treeEq0222 : B0222.tree = HexagonCover.NBand.M6700_6900.SplitData.node0222 := by
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

def B0221 : Block := .branch 170 ![10387129018270112868785490671698305, 618970609938501595666843138, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 2854495385411919762116571938898990272765886496, 374144419183933736414135461645000389649918481399872] ![(.leaf 0 (Common.fact 650).pointIds 650), (.leaf 1 (Common.fact 651).pointIds 651), (.leaf 2 (Common.fact 542).pointIds 542), (.leaf 3 (Common.fact 594).pointIds 594), (.leaf 4 (Common.fact 632).pointIds 632), (.leaf 5 (Common.fact 611).pointIds 611), B0222]
theorem treeEq0221 : B0221.tree = HexagonCover.NBand.M6700_6900.SplitData.node0221 := by
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
  · exact treeEq0222

def B0129 : Block := .branch 69 ![10387129018270112868785490671698305, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 2854495385411919762116571938898990272765886496, 374144419194822772155605801960838198432803788947520] ![B0130, B0221, (.leaf 2 (Common.fact 478).pointIds 478), (.leaf 3 (Common.fact 479).pointIds 479), (.leaf 4 (Common.fact 480).pointIds 480), (.leaf 5 (Common.fact 481).pointIds 481), (.leaf 6 (Common.fact 482).pointIds 482)]
theorem treeEq0129 : B0129.tree = HexagonCover.NBand.M6700_6900.SplitData.node0129 := by
  change Tree.branch (69 : Fin 175) _ = Tree.branch (69 : Fin 175) _
  apply congrArg (Tree.branch (69 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0130
  · exact treeEq0221
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0128 : Block := .branch 132 ![10387129018270112868785490671698305, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 2854495385411919762116571938898990272765886496, 374144419189378254284870786545424204713895497564224] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), (.leaf 4 (Common.fact 477).pointIds 477), (.leaf 5 (Common.fact 156).pointIds 156), B0129]
theorem treeEq0128 : B0128.tree = HexagonCover.NBand.M6700_6900.SplitData.node0128 := by
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
  · exact treeEq0129

theorem accepted0128 : B0128.accepted = true := by decide +kernel
theorem checked0128 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6700_6900.SplitData.node0128 (maskNeeds ![10387129018270112868785490671698305, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 2854495385411919762116571938898990272765886496, 374144419189378254284870786545424204713895497564224]) := by
  rw [← treeEq0128]
  exact B0128.sound accepted0128
#print axioms checked0128

end HexagonCover.NBand.M6700_6900.SplitTree.Run0001
