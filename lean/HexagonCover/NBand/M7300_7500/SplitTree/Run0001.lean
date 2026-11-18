import HexagonCover.NBand.M7300_7500.SplitData
import HexagonCover.NBand.M7300_7500.SplitTree.Run0000
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7300_7500.SplitTree.Run0001
open OwnerTree HexagonCover.NBand.M7300_7500

abbrev Block := Chunk (n := 172) (Certificate := Fin 1033) (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck

def Tip0138_0151 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node0151 ![10387129018874574625671300652204417, 618970019642691236961191426, 77919046967349146032132, 5846006549663894039735755165580962022322679603208, 182699203488105857128017958444269711768393187344, 982129100286366761032876207585342189208786669273120, 27924422060285443193961694874052517691456] HexagonCover.NBand.M7300_7500.SplitTree.Run0000.checked0151
def B0150 : Block := .branch 128 ![10387129018874574625671300652204417, 618970019642691236961191426, 77919046967349146032132, 5846006549323611672814816702117587414890911391752, 185553698873517776890134530383168702041158680592, 982129100286366761032876207585342189208786669273120, 27924422060285443193961694874052517691456] ![(.leaf 0 (Common.fact 261).pointIds 261), (.leaf 1 (Common.fact 262).pointIds 262), (.leaf 2 (Common.fact 263).pointIds 263), Tip0138_0151, (.leaf 4 (Common.fact 525).pointIds 525), (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 526).pointIds 526)]
theorem treeEq0150 : B0150.tree = HexagonCover.NBand.M7300_7500.SplitData.node0150 := by
  change Tree.branch (128 : Fin 172) _ = Tree.branch (128 : Fin 172) _
  apply congrArg (Tree.branch (128 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0149 : Block := .branch 138 ![10387129018874574625671300652204417, 618970019642691236961191426, 77919046967349146032132, 5846006549323611672894044864631851752484455342088, 185553350424374049849147943887570691910510149648, 982129100286366761032876207585342189208786669273120, 27924422060285443193961694874052517691456] ![(.leaf 0 (Common.fact 110).pointIds 110), (.leaf 1 (Common.fact 111).pointIds 111), (.leaf 2 (Common.fact 112).pointIds 112), (.leaf 3 (Common.fact 113).pointIds 113), B0150, (.leaf 5 (Common.fact 114).pointIds 114), (.leaf 6 (Common.fact 524).pointIds 524)]
theorem treeEq0149 : B0149.tree = HexagonCover.NBand.M7300_7500.SplitData.node0149 := by
  change Tree.branch (138 : Fin 172) _ = Tree.branch (138 : Fin 172) _
  apply congrArg (Tree.branch (138 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0150
  · rfl
  · rfl

def B0148 : Block := .branch 139 ![10387129018874574625671300652204417, 618970019642691236961191426, 77919046967349146032132, 5846006549323611672894044864631851752484455342088, 185553350424374049849147943887570691910510149648, 982129100286366761032876207585342189208786669273120, 27924422060285443193961694874052517691456] ![(.leaf 0 (Common.fact 104).pointIds 104), (.leaf 1 (Common.fact 105).pointIds 105), (.leaf 2 (Common.fact 106).pointIds 106), (.leaf 3 (Common.fact 107).pointIds 107), B0149, (.leaf 5 (Common.fact 108).pointIds 108), (.leaf 6 (Common.fact 523).pointIds 523)]
theorem treeEq0148 : B0148.tree = HexagonCover.NBand.M7300_7500.SplitData.node0148 := by
  change Tree.branch (139 : Fin 172) _ = Tree.branch (139 : Fin 172) _
  apply congrArg (Tree.branch (139 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0149
  · rfl
  · rfl

def B0147 : Block := .branch 140 ![10387129018874574625671300652204417, 618970019642691236961191426, 77919046967349146032132, 5846006549323611672894044864631851752484455342088, 185553350424374049849147943887570691910510149648, 982129100286366761032876207585342189208786669273120, 27924422060285443193961694874052517691456] ![(.leaf 0 (Common.fact 98).pointIds 98), (.leaf 1 (Common.fact 99).pointIds 99), (.leaf 2 (Common.fact 100).pointIds 100), (.leaf 3 (Common.fact 101).pointIds 101), B0148, (.leaf 5 (Common.fact 102).pointIds 102), (.leaf 6 (Common.fact 522).pointIds 522)]
theorem treeEq0147 : B0147.tree = HexagonCover.NBand.M7300_7500.SplitData.node0147 := by
  change Tree.branch (140 : Fin 172) _ = Tree.branch (140 : Fin 172) _
  apply congrArg (Tree.branch (140 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0148
  · rfl
  · rfl

def B0146 : Block := .branch 141 ![10387129018874574625671300652204417, 618970019642691236961191426, 77919046967349146032132, 5846006549323611672894044864631851752484455342088, 185553350424374049849147943887570691910510149648, 982129100286366761032876207585342189208786669273120, 27924422060285443193961694874052517691456] ![(.leaf 0 (Common.fact 92).pointIds 92), (.leaf 1 (Common.fact 93).pointIds 93), (.leaf 2 (Common.fact 94).pointIds 94), (.leaf 3 (Common.fact 95).pointIds 95), B0147, (.leaf 5 (Common.fact 96).pointIds 96), (.leaf 6 (Common.fact 521).pointIds 521)]
theorem treeEq0146 : B0146.tree = HexagonCover.NBand.M7300_7500.SplitData.node0146 := by
  change Tree.branch (141 : Fin 172) _ = Tree.branch (141 : Fin 172) _
  apply congrArg (Tree.branch (141 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0147
  · rfl
  · rfl

def B0145 : Block := .branch 142 ![10387129018874574625671300652204417, 618970019642691236961191426, 77919046967349146032132, 5846006549323611672894044864631851752484455342088, 185553350424374049849147943887570691910510149648, 982129100286366761032876207585342189208786669273120, 27924422060285443193961694874052517691456] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B0146, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 520).pointIds 520)]
theorem treeEq0145 : B0145.tree = HexagonCover.NBand.M7300_7500.SplitData.node0145 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0146
  · rfl
  · rfl

def B0144 : Block := .branch 165 ![10387129018874574625671300652204417, 618970019642691236961191426, 77919046967349146032132, 5846006549323611672894044864631851752484455342088, 185553350424374049849147943887570691910510149648, 935361047891777867650358292938421132579796827897888, 27924422060285443193961694874052517691456] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 519).pointIds 519), B0145, (.leaf 0 [] 0)]
theorem treeEq0144 : B0144.tree = HexagonCover.NBand.M7300_7500.SplitData.node0144 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0145
  · rfl

def B0143 : Block := .branch 167 ![10387129018874574625671300652204417, 618970019642691236961191426, 77919046967349146032132, 5846006549323611672894044864631851752484455342088, 185553350424374049849147943887570691910510149648, 748288838313422294120286634350736906063837462396960, 27924422060285443193961694874052517691456] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 517).pointIds 517), B0144, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq0143 : B0143.tree = HexagonCover.NBand.M7300_7500.SplitData.node0143 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0144
  · rfl

def B0142 : Block := .branch 143 ![10387129018874574625671300652204417, 618970019642691236961191426, 77919046967349146032132, 5846006549323611672894044864631851752484455342088, 185542200051774784537577176028434367729757159440, 748288838313464829416151751658669827889766433423392, 27924422060285443193961694874052517691456] ![(.leaf 0 (Common.fact 507).pointIds 507), (.leaf 1 (Common.fact 508).pointIds 508), (.leaf 2 (Common.fact 509).pointIds 509), (.leaf 3 (Common.fact 510).pointIds 510), B0143, (.leaf 5 (Common.fact 511).pointIds 511), (.leaf 6 (Common.fact 512).pointIds 512)]
theorem treeEq0142 : B0142.tree = HexagonCover.NBand.M7300_7500.SplitData.node0142 := by
  change Tree.branch (143 : Fin 172) _ = Tree.branch (143 : Fin 172) _
  apply congrArg (Tree.branch (143 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0143
  · rfl
  · rfl

def B0141 : Block := .branch 162 ![10387129018874574625671300652204417, 618970019642691236961191426, 77919046967349146032132, 79305533766719673860725170184, 185542200051774784537577176028434367729757159440, 748288838313464829416151751658669827889766433423392, 27924422060285443193961694874052517691456] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), B0142, (.leaf 4 (Common.fact 505).pointIds 505), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 506).pointIds 506)]
theorem treeEq0141 : B0141.tree = HexagonCover.NBand.M7300_7500.SplitData.node0141 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0142
  · rfl
  · rfl
  · rfl

def B0140 : Block := .branch 124 ![10387129018874574625671300652204417, 618970019642691236961191426, 77919046967349146032132, 79305533766719673860725170184, 185542200051774784537577176028434367729757159440, 748288838313464829416151751658669827889766433423392, 27903154412352884539995233961088032178240] ![(.leaf 0 (Common.fact 504).pointIds 504), (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), (.leaf 4 (Common.fact 214).pointIds 214), (.leaf 5 (Common.fact 215).pointIds 215), B0141]
theorem treeEq0140 : B0140.tree = HexagonCover.NBand.M7300_7500.SplitData.node0140 := by
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
  · exact treeEq0141

def B0175 : Block := .branch 124 ![730750818665461843695559486013398570820624712065, 1538, 6148, 24584, 98320, 393248, 2993155353276147812697928940219045080363999392432192] ![(.leaf 0 (Common.fact 564).pointIds 564), (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), (.leaf 4 (Common.fact 214).pointIds 214), (.leaf 5 (Common.fact 215).pointIds 215), (.leaf 6 (Common.fact 535).pointIds 535)]
theorem treeEq0175 : B0175.tree = HexagonCover.NBand.M7300_7500.SplitData.node0175 := by
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
  · rfl

def B0174 : Block := .branch 159 ![10384593717069655257060992658440577, 619574482552498551548544514, 6148, 24584, 98320, 393248, 2993155353276147812697928940219045080363999392432192] ![B0175, (.leaf 1 (Common.fact 562).pointIds 562), (.leaf 2 (Common.fact 226).pointIds 226), (.leaf 3 (Common.fact 227).pointIds 227), (.leaf 4 (Common.fact 228).pointIds 228), (.leaf 5 (Common.fact 229).pointIds 229), (.leaf 6 (Common.fact 563).pointIds 563)]
theorem treeEq0174 : B0174.tree = HexagonCover.NBand.M7300_7500.SplitData.node0174 := by
  change Tree.branch (159 : Fin 172) _ = Tree.branch (159 : Fin 172) _
  apply congrArg (Tree.branch (159 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0175
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0173 : Block := .branch 160 ![10384593717069655257060992658440577, 619574482552498551548544514, 6148, 24584, 98320, 393248, 2993155353276147812697928940219045080363999392432192] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 473).pointIds 473), B0174, (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 561).pointIds 561)]
theorem treeEq0173 : B0173.tree = HexagonCover.NBand.M7300_7500.SplitData.node0173 := by
  change Tree.branch (160 : Fin 172) _ = Tree.branch (160 : Fin 172) _
  apply congrArg (Tree.branch (160 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0174
  · rfl
  · rfl
  · rfl
  · rfl

def B0172 : Block := .branch 162 ![10384593717069655257060992658440577, 619574482552498551548544514, 6148, 24584, 185542200051774784537577176028434367729757159440, 393248, 2993155353276147812697928940219045080363999392432192] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), B0173, (.leaf 4 (Common.fact 505).pointIds 505), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 560).pointIds 560)]
theorem treeEq0172 : B0172.tree = HexagonCover.NBand.M7300_7500.SplitData.node0172 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0173
  · rfl
  · rfl
  · rfl

def B0171 : Block := .branch 171 ![374144419156711157447272335446070464706263501504897, 619574482552498551548544514, 77919046967349146032132, 77371252455336267181219848, 185542200051774784537577176028434367729757159440, 748288838313422294120286634350736906063837462396960, 22458636216782402816097456108649544417344] ![(.leaf 0 (Common.fact 555).pointIds 555), (.leaf 1 (Common.fact 556).pointIds 556), (.leaf 2 (Common.fact 547).pointIds 547), (.leaf 3 (Common.fact 557).pointIds 557), (.leaf 4 (Common.fact 558).pointIds 558), (.leaf 5 (Common.fact 559).pointIds 559), B0172]
theorem treeEq0171 : B0171.tree = HexagonCover.NBand.M7300_7500.SplitData.node0171 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0172

def B0139 : Block := .branch 79 ![374144419156711157447272335446070464706263501504897, 618970019642691236961191426, 77919046967349146032132, 79305533766719673860725170184, 185542200051774784537577176028434367729757159440, 748288838313464829416151751658669827889766433423392, 27903154412352884539995233961088032178240] ![B0140, B0171, (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), (.leaf 6 (Common.fact 503).pointIds 503)]
theorem treeEq0139 : B0139.tree = HexagonCover.NBand.M7300_7500.SplitData.node0139 := by
  change Tree.branch (79 : Fin 172) _ = Tree.branch (79 : Fin 172) _
  apply congrArg (Tree.branch (79 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0140
  · exact treeEq0171
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0138 : Block := .branch 169 ![374144419156711157447272335446070464706263501504897, 618970019642691236961191426, 77919046967349146032132, 79305533766719673860725170184, 185542200051774784537577176028434367729757159440, 42535295865117307932921825928971419680, 27903154412352884539995233961088032178240] ![(.leaf 0 (Common.fact 497).pointIds 497), (.leaf 1 (Common.fact 498).pointIds 498), (.leaf 2 (Common.fact 499).pointIds 499), (.leaf 3 (Common.fact 500).pointIds 500), (.leaf 4 (Common.fact 501).pointIds 501), B0139, (.leaf 6 (Common.fact 502).pointIds 502)]
theorem treeEq0138 : B0138.tree = HexagonCover.NBand.M7300_7500.SplitData.node0138 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0139
  · rfl

theorem accepted0138 : B0138.accepted = true := by decide +kernel
theorem checked0138 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node0138 (maskNeeds ![374144419156711157447272335446070464706263501504897, 618970019642691236961191426, 77919046967349146032132, 79305533766719673860725170184, 185542200051774784537577176028434367729757159440, 42535295865117307932921825928971419680, 27903154412352884539995233961088032178240]) := by
  rw [← treeEq0138]
  exact B0138.sound accepted0138
#print axioms checked0138

def Tip0092_0103 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node0103 ![5192296859139290538337810916573569, 618970019642691236961191426, 77919046967349146032132, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 42535295865117307932921825928971419680, 2860092371050683607899149062692309487811297344] HexagonCover.NBand.M7300_7500.SplitTree.Run0000.checked0103
def B0122 : Block := .branch 170 ![2535301804919368610307993764225, 618970019642691236961191426, 77919046967349146032132, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 42535295865117307932921825928971419680, 2854517184756243248972299960752677893764022336] ![(.leaf 0 (Common.fact 471).pointIds 471), (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 463).pointIds 463), (.leaf 3 (Common.fact 461).pointIds 461), (.leaf 4 (Common.fact 459).pointIds 459), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 472).pointIds 472)]
theorem treeEq0122 : B0122.tree = HexagonCover.NBand.M7300_7500.SplitData.node0122 := by
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

def B0102 : Block := .branch 112 ![2535301804919368610307993764225, 618970019642691236961191426, 77919046967349146032132, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 42535295865117307932921825928971419680, 2860092371050683607899149062692309487811297344] ![Tip0092_0103, (.leaf 1 (Common.fact 421).pointIds 421), (.leaf 2 (Common.fact 422).pointIds 422), (.leaf 3 (Common.fact 423).pointIds 423), (.leaf 4 (Common.fact 424).pointIds 424), (.leaf 5 (Common.fact 425).pointIds 425), B0122]
theorem treeEq0102 : B0102.tree = HexagonCover.NBand.M7300_7500.SplitData.node0102 := by
  change Tree.branch (112 : Fin 172) _ = Tree.branch (112 : Fin 172) _
  apply congrArg (Tree.branch (112 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0122

def B0101 : Block := .branch 124 ![2535301804919368610307993764225, 618970019642691236961191426, 77919046967349146032132, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 42535295865117307932921825928971419680, 2860092349783035675340495096231396523325784128] ![(.leaf 0 (Common.fact 420).pointIds 420), (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), (.leaf 4 (Common.fact 214).pointIds 214), (.leaf 5 (Common.fact 215).pointIds 215), B0102]
theorem treeEq0101 : B0101.tree = HexagonCover.NBand.M7300_7500.SplitData.node0101 := by
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
  · exact treeEq0102

def B0124 : Block := .branch 170 ![374144419156711147062678618376415207645270843064705, 619574482552498551548544514, 1461501637330902918203684835077466261090755155972, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 42535295865117307932921825928971419680, 2854517163483403019555111166663234432949289024] ![(.leaf 0 (Common.fact 474).pointIds 474), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 461).pointIds 461), (.leaf 4 (Common.fact 459).pointIds 459), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq0124 : B0124.tree = HexagonCover.NBand.M7300_7500.SplitData.node0124 := by
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

def B0123 : Block := .branch 160 ![374144419156711147062678618376415207645270843064705, 619574482552498551548544514, 2361183241434822612996, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 42535295865117307932921825928971419680, 2860092349783035675340495096231396523325784128] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 473).pointIds 473), B0124, (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 426).pointIds 426)]
theorem treeEq0123 : B0123.tree = HexagonCover.NBand.M7300_7500.SplitData.node0123 := by
  change Tree.branch (160 : Fin 172) _ = Tree.branch (160 : Fin 172) _
  apply congrArg (Tree.branch (160 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0124
  · rfl
  · rfl
  · rfl
  · rfl

def B0100 : Block := .branch 79 ![374144419156711147062678618376415207645270843064705, 618970019642691236961191426, 77919046967349146032132, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 42535295865117307932921825928971419680, 2860092349783035675340495096231396523325784128] ![B0101, B0123, (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), (.leaf 6 (Common.fact 419).pointIds 419)]
theorem treeEq0100 : B0100.tree = HexagonCover.NBand.M7300_7500.SplitData.node0100 := by
  change Tree.branch (79 : Fin 172) _ = Tree.branch (79 : Fin 172) _
  apply congrArg (Tree.branch (79 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0101
  · exact treeEq0123
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0126 : Block := .branch 170 ![374144419156711147062678618375824911834912137412993, 618970609938501595666843138, 1461501637330902918203684835077466261090755155972, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 42535295865117307932921825928971419680, 2854517163483403019555111166663234432949289024] ![(.leaf 0 (Common.fact 478).pointIds 478), (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 461).pointIds 461), (.leaf 4 (Common.fact 459).pointIds 459), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq0126 : B0126.tree = HexagonCover.NBand.M7300_7500.SplitData.node0126 := by
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

def B0125 : Block := .branch 160 ![374144419156711147062678618375824911834912137412993, 618970609938501595666843138, 2361183241434822612996, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 42535295865117307932921825928971419680, 2860092349783035675340495096231396523325784128] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 477).pointIds 477), B0126, (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 426).pointIds 426)]
theorem treeEq0125 : B0125.tree = HexagonCover.NBand.M7300_7500.SplitData.node0125 := by
  change Tree.branch (160 : Fin 172) _ = Tree.branch (160 : Fin 172) _
  apply congrArg (Tree.branch (160 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0126
  · rfl
  · rfl
  · rfl
  · rfl

def B0099 : Block := .branch 69 ![374144419156711147062678618375824911834912137412993, 618970019642691236961191426, 77919046967349146032132, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 42535295865117307932921825928971419680, 2860092349783035675340495096231396523325784128] ![B0100, B0125, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 418).pointIds 418)]
theorem treeEq0099 : B0099.tree = HexagonCover.NBand.M7300_7500.SplitData.node0099 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0100
  · exact treeEq0125
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0098 : Block := .branch 137 ![374144419156711147062678618375824911834912137412993, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 11874700803313586534923492924246526317860472586256, 42535295865117307932921825928971419680, 2860092349783035675340495096231396523325784128] ![(.leaf 0 (Common.fact 256).pointIds 256), (.leaf 1 (Common.fact 257).pointIds 257), (.leaf 2 (Common.fact 258).pointIds 258), B0099, (.leaf 4 (Common.fact 413).pointIds 413), (.leaf 5 (Common.fact 260).pointIds 260), (.leaf 0 [] 0)]
theorem treeEq0098 : B0098.tree = HexagonCover.NBand.M7300_7500.SplitData.node0098 := by
  change Tree.branch (137 : Fin 172) _ = Tree.branch (137 : Fin 172) _
  apply congrArg (Tree.branch (137 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0099
  · rfl
  · rfl
  · rfl

def B0097 : Block := .branch 163 ![374144419156711147062678618375824911834912137412993, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 182687704666363189294014262516262160613012242448, 42535295865117307932921825928971419680, 2860092349783035675340495096231396523325784128] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B0098, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 412).pointIds 412)]
theorem treeEq0097 : B0097.tree = HexagonCover.NBand.M7300_7500.SplitData.node0097 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0098
  · rfl
  · rfl

def B0096 : Block := .branch 151 ![374144419156711147062678618375824911834912137412993, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 182687704666363189294014262516262160613012242448, 42535295865117307932921825928971419680, 5596964371115913223923157332406250560290880] ![(.leaf 0 (Common.fact 250).pointIds 250), (.leaf 1 (Common.fact 251).pointIds 251), (.leaf 2 (Common.fact 252).pointIds 252), (.leaf 3 (Common.fact 253).pointIds 253), (.leaf 4 (Common.fact 411).pointIds 411), (.leaf 5 (Common.fact 255).pointIds 255), B0097]
theorem treeEq0096 : B0096.tree = HexagonCover.NBand.M7300_7500.SplitData.node0096 := by
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
  · exact treeEq0097

def B0095 : Block := .branch 157 ![374144419156711147062678618375824911834912137412993, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 42535295865117307932921825928971419680, 5596964371115913223923157332406250560290880] ![(.leaf 0 (Common.fact 175).pointIds 175), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), B0096, (.leaf 5 (Common.fact 179).pointIds 179), (.leaf 0 [] 0)]
theorem treeEq0095 : B0095.tree = HexagonCover.NBand.M7300_7500.SplitData.node0095 := by
  change Tree.branch (157 : Fin 172) _ = Tree.branch (157 : Fin 172) _
  apply congrArg (Tree.branch (157 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0096
  · rfl
  · rfl

def B0094 : Block := .branch 125 ![374144419156711147062678618375824911834912137412993, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 393248, 5596964371115913223923157332406250560290880] ![(.leaf 0 (Common.fact 410).pointIds 410), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B0095, (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq0094 : B0094.tree = HexagonCover.NBand.M7300_7500.SplitData.node0094 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0095
  · rfl

def B0093 : Block := .branch 168 ![2535301200456458802993406411137, 618970020002979207150831106, 77937529740219874547716, 116056878683004400771817480, 713623846353304459082801411451530724212047888, 393248, 5596964371115913223923157332406250560290880] ![B0094, (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 409).pointIds 409)]
theorem treeEq0093 : B0093.tree = HexagonCover.NBand.M7300_7500.SplitData.node0093 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0094
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0092 : Block := .branch 142 ![2535301200456458802993406411137, 618970020002979207150831106, 77937529740219874547716, 116056878683004400771817480, 713623846353304459082801411451530724212047888, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), (.leaf 4 (Common.fact 408).pointIds 408), (.leaf 5 (Common.fact 144).pointIds 144), B0093]
theorem treeEq0092 : B0092.tree = HexagonCover.NBand.M7300_7500.SplitData.node0092 := by
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
  · exact treeEq0093

theorem accepted0092 : B0092.accepted = true := by decide +kernel
theorem checked0092 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node0092 (maskNeeds ![2535301200456458802993406411137, 618970020002979207150831106, 77937529740219874547716, 116056878683004400771817480, 713623846353304459082801411451530724212047888, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0092]
  exact B0092.sound accepted0092
#print axioms checked0092

def Tip0091_0138 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node0138 ![374144419156711157447272335446070464706263501504897, 618970019642691236961191426, 77919046967349146032132, 79305533766719673860725170184, 185542200051774784537577176028434367729757159440, 42535295865117307932921825928971419680, 27903154412352884539995233961088032178240] checked0138
def Tip0091_0092 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node0092 ![2535301200456458802993406411137, 618970020002979207150831106, 77937529740219874547716, 116056878683004400771817480, 713623846353304459082801411451530724212047888, 393248, 21778071483257438539227764244160183795776] checked0092
def B0180 : Block := .branch 124 ![730750818665461843695559486013398570820624712065, 1538, 6148, 24584, 98320, 393248, 2993155353276147812697928940219045080363999392432192] ![(.leaf 0 (Common.fact 564).pointIds 564), (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), (.leaf 4 (Common.fact 214).pointIds 214), (.leaf 5 (Common.fact 215).pointIds 215), (.leaf 6 (Common.fact 535).pointIds 535)]
theorem treeEq0180 : B0180.tree = HexagonCover.NBand.M7300_7500.SplitData.node0180 := by
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
  · rfl

def B0179 : Block := .branch 159 ![10384593717069655257060992658440577, 618970609938501595666843138, 6148, 24584, 98320, 393248, 2993155353276147812697928940219045080363999392432192] ![B0180, (.leaf 1 (Common.fact 568).pointIds 568), (.leaf 2 (Common.fact 226).pointIds 226), (.leaf 3 (Common.fact 227).pointIds 227), (.leaf 4 (Common.fact 228).pointIds 228), (.leaf 5 (Common.fact 229).pointIds 229), (.leaf 6 (Common.fact 563).pointIds 563)]
theorem treeEq0179 : B0179.tree = HexagonCover.NBand.M7300_7500.SplitData.node0179 := by
  change Tree.branch (159 : Fin 172) _ = Tree.branch (159 : Fin 172) _
  apply congrArg (Tree.branch (159 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0180
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0178 : Block := .branch 160 ![10384593717069655257060992658440577, 618970609938501595666843138, 6148, 24584, 98320, 393248, 2993155353276147812697928940219045080363999392432192] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 477).pointIds 477), B0179, (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 561).pointIds 561)]
theorem treeEq0178 : B0178.tree = HexagonCover.NBand.M7300_7500.SplitData.node0178 := by
  change Tree.branch (160 : Fin 172) _ = Tree.branch (160 : Fin 172) _
  apply congrArg (Tree.branch (160 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0179
  · rfl
  · rfl
  · rfl
  · rfl

def B0177 : Block := .branch 162 ![10384593717069655257060992658440577, 618970609938501595666843138, 6148, 24584, 185542200051774784537577176028434367729757159440, 393248, 2993155353276147812697928940219045080363999392432192] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), B0178, (.leaf 4 (Common.fact 505).pointIds 505), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 560).pointIds 560)]
theorem treeEq0177 : B0177.tree = HexagonCover.NBand.M7300_7500.SplitData.node0177 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0178
  · rfl
  · rfl
  · rfl

def B0176 : Block := .branch 171 ![374144419156711157447272335445480168895904795853185, 618970609938501595666843138, 77919046967349146032132, 77371252455336267181219848, 185542200051774784537577176028434367729757159440, 42535295865117307932921825928971419680, 22458636216782402816097456108649544417344] ![(.leaf 0 (Common.fact 565).pointIds 565), (.leaf 1 (Common.fact 566).pointIds 566), (.leaf 2 (Common.fact 547).pointIds 547), (.leaf 3 (Common.fact 557).pointIds 557), (.leaf 4 (Common.fact 558).pointIds 558), (.leaf 5 (Common.fact 567).pointIds 567), B0177]
theorem treeEq0176 : B0176.tree = HexagonCover.NBand.M7300_7500.SplitData.node0176 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0177

def B0137 : Block := .branch 69 ![374144419156711157447272335445480168895904795853185, 618970019642691236961191426, 77919046967349146032132, 79305533766719673860725170184, 185542200051774784537577176028434367729757159440, 42535295865117307932921825928971419680, 27903154412352884539995233961088032178240] ![Tip0091_0138, B0176, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 496).pointIds 496)]
theorem treeEq0137 : B0137.tree = HexagonCover.NBand.M7300_7500.SplitData.node0137 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0176
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0136 : Block := .branch 113 ![374144419156711147062678618375824911834912137412993, 618970019642691236961191426, 77919046967349146032132, 79305533766719673860725170184, 185542200051774784537577176028434367729757159440, 42535295865117307932921825928971419680, 27903154412352884539995233961088032178240] ![B0137, (.leaf 1 (Common.fact 239).pointIds 239), (.leaf 2 (Common.fact 240).pointIds 240), (.leaf 3 (Common.fact 241).pointIds 241), (.leaf 4 (Common.fact 242).pointIds 242), (.leaf 5 (Common.fact 243).pointIds 243), (.leaf 6 (Common.fact 495).pointIds 495)]
theorem treeEq0136 : B0136.tree = HexagonCover.NBand.M7300_7500.SplitData.node0136 := by
  change Tree.branch (113 : Fin 172) _ = Tree.branch (113 : Fin 172) _
  apply congrArg (Tree.branch (113 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0137
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0135 : Block := .branch 129 ![374144419156711147062678618375824911834912137412993, 618970019642691236961191426, 77919046967349146032132, 79305533766719673860725170184, 185542200051774784537577176028434367729757159440, 42535295865117307932921825928971419680, 27222589678511007613068484746224495755328] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 298).pointIds 298), (.leaf 2 (Common.fact 299).pointIds 299), (.leaf 3 (Common.fact 300).pointIds 300), (.leaf 4 (Common.fact 494).pointIds 494), (.leaf 5 (Common.fact 301).pointIds 301), B0136]
theorem treeEq0135 : B0135.tree = HexagonCover.NBand.M7300_7500.SplitData.node0135 := by
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
  · exact treeEq0136

def B0134 : Block := .branch 130 ![374144419156711147062678618375824911834912137412993, 618970019642691236961191426, 77919046967349146032132, 79305533766719673860725170184, 185542200051774784537577176028434367729757159440, 42535295865117307932921825928971419680, 27222589678511007613068484746224495755328] ![(.leaf 0 (Common.fact 488).pointIds 488), (.leaf 1 (Common.fact 489).pointIds 489), (.leaf 2 (Common.fact 490).pointIds 490), (.leaf 3 (Common.fact 491).pointIds 491), (.leaf 4 (Common.fact 492).pointIds 492), (.leaf 5 (Common.fact 493).pointIds 493), B0135]
theorem treeEq0134 : B0134.tree = HexagonCover.NBand.M7300_7500.SplitData.node0134 := by
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
  · exact treeEq0135

def B0133 : Block := .branch 131 ![374144419156711147062678618375824911834912137412993, 618970019642691236961191426, 77919046967349146032132, 79305533766719673860725170184, 185542200051774784537577176028434367729757159440, 42535295865117307932921825928971419680, 27222589678511007613068484746224495755328] ![(.leaf 0 (Common.fact 482).pointIds 482), (.leaf 1 (Common.fact 483).pointIds 483), (.leaf 2 (Common.fact 484).pointIds 484), (.leaf 3 (Common.fact 485).pointIds 485), (.leaf 4 (Common.fact 486).pointIds 486), (.leaf 5 (Common.fact 487).pointIds 487), B0134]
theorem treeEq0133 : B0133.tree = HexagonCover.NBand.M7300_7500.SplitData.node0133 := by
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
  · exact treeEq0134

def B0132 : Block := .branch 151 ![374144419156711147062678618375824911834912137412993, 618970019642691236961191426, 77919046967349146032132, 79305533766719673860725170184, 182687704666362864775460604089535377456991666192, 42535295865117307932921825928971419680, 27222589678511007613068484746224495755328] ![(.leaf 0 (Common.fact 250).pointIds 250), (.leaf 1 (Common.fact 251).pointIds 251), (.leaf 2 (Common.fact 252).pointIds 252), (.leaf 3 (Common.fact 253).pointIds 253), B0133, (.leaf 5 (Common.fact 255).pointIds 255), (.leaf 6 (Common.fact 481).pointIds 481)]
theorem treeEq0132 : B0132.tree = HexagonCover.NBand.M7300_7500.SplitData.node0132 := by
  change Tree.branch (151 : Fin 172) _ = Tree.branch (151 : Fin 172) _
  apply congrArg (Tree.branch (151 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0133
  · rfl
  · rfl

def B0131 : Block := .branch 132 ![374144419156711147062678618375824911834912137412993, 618970019642691236961191426, 77919046967349146032132, 79305533766719673860725170184, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 21778071807775992197654491027316204372032] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 196).pointIds 196), (.leaf 5 (Common.fact 197).pointIds 197), B0132]
theorem treeEq0131 : B0131.tree = HexagonCover.NBand.M7300_7500.SplitData.node0131 := by
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

def B0130 : Block := .branch 133 ![374144419156711147062678618375824911834912137412993, 618970019642691236961191426, 77919046967349146032132, 79305533766719673860725170184, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 21778071807775992197654491027316204372032] ![(.leaf 0 (Common.fact 180).pointIds 180), (.leaf 1 (Common.fact 181).pointIds 181), (.leaf 2 (Common.fact 182).pointIds 182), (.leaf 3 (Common.fact 183).pointIds 183), (.leaf 4 (Common.fact 184).pointIds 184), (.leaf 5 (Common.fact 185).pointIds 185), B0131]
theorem treeEq0130 : B0130.tree = HexagonCover.NBand.M7300_7500.SplitData.node0130 := by
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

def B0129 : Block := .branch 157 ![374144419156711147062678618375824911834912137412993, 618970019642691236961191426, 77919046967349146032132, 79305533766719673860725170184, 713623846352979940529142984724747568191471632, 42535295865117307932921825928971419680, 21778071807775992197654491027316204372032] ![(.leaf 0 (Common.fact 175).pointIds 175), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), B0130, (.leaf 5 (Common.fact 179).pointIds 179), (.leaf 0 [] 0)]
theorem treeEq0129 : B0129.tree = HexagonCover.NBand.M7300_7500.SplitData.node0129 := by
  change Tree.branch (157 : Fin 172) _ = Tree.branch (157 : Fin 172) _
  apply congrArg (Tree.branch (157 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0130
  · rfl
  · rfl

def B0128 : Block := .branch 125 ![374144419156711147062678618375824911834912137412993, 618970019642691236961191426, 77919046967349146032132, 79305533766719673860725170184, 713623846352979940529142984724747568191471632, 393248, 21778071807775992197654491027316204372032] ![(.leaf 0 (Common.fact 410).pointIds 410), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B0129, (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq0128 : B0128.tree = HexagonCover.NBand.M7300_7500.SplitData.node0128 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0129
  · rfl

def B0127 : Block := .branch 168 ![2535301200456458802993406411137, 618970020002979207150831106, 77937529740219874547716, 79344219392947341994315767816, 713623846352979940529142984724747568191471632, 393248, 21778071807775992197654491027316204372032] ![B0128, (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 480).pointIds 480)]
theorem treeEq0127 : B0127.tree = HexagonCover.NBand.M7300_7500.SplitData.node0127 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0128
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0091 : Block := .branch 108 ![2535301200456458802993406411137, 618970020002979207150831106, 77937529740219874547716, 79344219392947341994315767816, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), Tip0091_0092, (.leaf 5 (Common.fact 308).pointIds 308), B0127]
theorem treeEq0091 : B0091.tree = HexagonCover.NBand.M7300_7500.SplitData.node0091 := by
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
  · exact treeEq0127

theorem accepted0091 : B0091.accepted = true := by decide +kernel
theorem checked0091 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node0091 (maskNeeds ![2535301200456458802993406411137, 618970020002979207150831106, 77937529740219874547716, 79344219392947341994315767816, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0091]
  exact B0091.sound accepted0091
#print axioms checked0091

def Tip0090_0091 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node0091 ![2535301200456458802993406411137, 618970020002979207150831106, 77937529740219874547716, 79344219392947341994315767816, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] checked0091
def B0192 : Block := .branch 170 ![374144419156711147060143317175368453031918731002241, 618970019642691236961191426, 77919046967349146032132, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 42535295865117307932921825928971419680, 2854517163483405554856311623122037426355699776] ![(.leaf 0 (Common.fact 580).pointIds 580), (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 463).pointIds 463), (.leaf 3 (Common.fact 461).pointIds 461), (.leaf 4 (Common.fact 459).pointIds 459), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 581).pointIds 581)]
theorem treeEq0192 : B0192.tree = HexagonCover.NBand.M7300_7500.SplitData.node0192 := by
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

def B0191 : Block := .branch 108 ![374144419156711147060143317175368453031918731002241, 618970019642691236961191426, 77919046967349146032132, 174224571863520609350126482009466096082952, 11874700803313586210404939265819799534704452010000, 42535295865117307932921825928971419680, 2854517163483405554856311623122037426355699776] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), B0192, (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 579).pointIds 579)]
theorem treeEq0191 : B0191.tree = HexagonCover.NBand.M7300_7500.SplitData.node0191 := by
  change Tree.branch (108 : Fin 172) _ = Tree.branch (108 : Fin 172) _
  apply congrArg (Tree.branch (108 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0192
  · rfl
  · rfl

def B0190 : Block := .branch 119 ![374144419156711147060143317175368453031918731002241, 618970019642691236961191426, 77919046967349146032132, 174224571863520609350126482009466096082952, 11874700803313586210404939265819799534704452010000, 42535295865117307932921825928971419680, 2854517163483405554856311623122037426355699776] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), B0191, (.leaf 5 (Common.fact 151).pointIds 151), (.leaf 6 (Common.fact 578).pointIds 578)]
theorem treeEq0190 : B0190.tree = HexagonCover.NBand.M7300_7500.SplitData.node0190 := by
  change Tree.branch (119 : Fin 172) _ = Tree.branch (119 : Fin 172) _
  apply congrArg (Tree.branch (119 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0191
  · rfl
  · rfl

def B0189 : Block := .branch 129 ![374144419156711147060143317175368453031918731002241, 618970019642691236961191426, 77919046967349146032132, 174224571863599837512640746347059640033288, 11874700803313586210404939265819799534704452010000, 42535295865117307932921825928971419680, 2854517163483405554856311623122037426355699776] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 298).pointIds 298), (.leaf 2 (Common.fact 299).pointIds 299), (.leaf 3 (Common.fact 300).pointIds 300), B0190, (.leaf 5 (Common.fact 301).pointIds 301), (.leaf 6 (Common.fact 577).pointIds 577)]
theorem treeEq0189 : B0189.tree = HexagonCover.NBand.M7300_7500.SplitData.node0189 := by
  change Tree.branch (129 : Fin 172) _ = Tree.branch (129 : Fin 172) _
  apply congrArg (Tree.branch (129 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0190
  · rfl
  · rfl

def B0188 : Block := .branch 137 ![374144419156711147060143317175368453031918731002241, 618970019642691236961191426, 77919046967349146032132, 79344219392947341994315767816, 11874700803313586210404939265819799534704452010000, 42535295865117307932921825928971419680, 2854517163483405554856311623122037426355699776] ![(.leaf 0 (Common.fact 256).pointIds 256), (.leaf 1 (Common.fact 257).pointIds 257), (.leaf 2 (Common.fact 258).pointIds 258), B0189, (.leaf 4 (Common.fact 576).pointIds 576), (.leaf 5 (Common.fact 260).pointIds 260), (.leaf 0 [] 0)]
theorem treeEq0188 : B0188.tree = HexagonCover.NBand.M7300_7500.SplitData.node0188 := by
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

def B0187 : Block := .branch 97 ![374144419156711147060143317175368453031918731002241, 618970019642691236961191426, 77919046967349146032132, 79344219392947341994315767816, 11874700803313586210404939265819799534704452010000, 42535295865117307932921825928971419680, 2860092349783038210641695552690199516732194880] ![(.leaf 0 (Common.fact 279).pointIds 279), (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 281).pointIds 281), B0188, (.leaf 4 (Common.fact 574).pointIds 574), (.leaf 5 (Common.fact 283).pointIds 283), (.leaf 6 (Common.fact 575).pointIds 575)]
theorem treeEq0187 : B0187.tree = HexagonCover.NBand.M7300_7500.SplitData.node0187 := by
  change Tree.branch (97 : Fin 172) _ = Tree.branch (97 : Fin 172) _
  apply congrArg (Tree.branch (97 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0188
  · rfl
  · rfl
  · rfl

def B0186 : Block := .branch 151 ![374144419156711147060143317175368453031918731002241, 618970019642691236961191426, 77919046967349146032132, 79344219392947341994315767816, 11874700803313586210404939265819799534704452010000, 42535295865117307932921825928971419680, 5596964371118448525123613791209243966701632] ![(.leaf 0 (Common.fact 250).pointIds 250), (.leaf 1 (Common.fact 251).pointIds 251), (.leaf 2 (Common.fact 252).pointIds 252), (.leaf 3 (Common.fact 253).pointIds 253), (.leaf 4 (Common.fact 573).pointIds 573), (.leaf 5 (Common.fact 255).pointIds 255), B0187]
theorem treeEq0186 : B0186.tree = HexagonCover.NBand.M7300_7500.SplitData.node0186 := by
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
  · exact treeEq0187

def B0185 : Block := .branch 157 ![374144419156711147060143317175368453031918731002241, 618970019642691236961191426, 77919046967349146032132, 79344219392947341994315767816, 11692013098647223345629478661730264157247460442128, 42535295865117307932921825928971419680, 5596964371118448525123613791209243966701632] ![(.leaf 0 (Common.fact 175).pointIds 175), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), B0186, (.leaf 5 (Common.fact 179).pointIds 179), (.leaf 0 [] 0)]
theorem treeEq0185 : B0185.tree = HexagonCover.NBand.M7300_7500.SplitData.node0185 := by
  change Tree.branch (157 : Fin 172) _ = Tree.branch (157 : Fin 172) _
  apply congrArg (Tree.branch (157 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0186
  · rfl
  · rfl

def B0184 : Block := .branch 125 ![374144419156711147060143317175368453031918731002241, 618970019642691236961191426, 77919046967349146032132, 79344219392947341994315767816, 11692013098647223345629478661730264157247460442128, 393248, 5596964371118448525123613791209243966701632] ![(.leaf 0 (Common.fact 572).pointIds 572), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B0185, (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq0184 : B0184.tree = HexagonCover.NBand.M7300_7500.SplitData.node0184 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0185
  · rfl

def B0183 : Block := .branch 168 ![385, 618970020002979207150831106, 77937529740219874547716, 79344219392947341994315767816, 11692726722493576325570007804714988904815651815440, 393248, 5596964371118448525123613791209243966701632] ![B0184, (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 571).pointIds 571)]
theorem treeEq0183 : B0183.tree = HexagonCover.NBand.M7300_7500.SplitData.node0183 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0184
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0182 : Block := .branch 142 ![385, 618970020002979207150831106, 77937529740219874547716, 79344219392947341994315767816, 11692726722493576325570007804714988904815651815440, 393248, 21778071485792739739684223047153590206528] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), (.leaf 4 (Common.fact 570).pointIds 570), (.leaf 5 (Common.fact 144).pointIds 144), B0183]
theorem treeEq0182 : B0182.tree = HexagonCover.NBand.M7300_7500.SplitData.node0182 := by
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
  · exact treeEq0183

def B0181 : Block := .branch 163 ![385, 618970020002979207150831106, 77937529740219874547716, 79344219392947341994315767816, 713623846352979940529142984724747568191471632, 393248, 21778071485792739739684223047153590206528] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B0182, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 569).pointIds 569)]
theorem treeEq0181 : B0181.tree = HexagonCover.NBand.M7300_7500.SplitData.node0181 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0182
  · rfl
  · rfl

def B0090 : Block := .branch 101 ![385, 618970020002979207150831106, 77937529740219874547716, 79344219392947341994315767816, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![Tip0090_0091, (.leaf 1 (Common.fact 403).pointIds 403), (.leaf 2 (Common.fact 404).pointIds 404), (.leaf 3 (Common.fact 405).pointIds 405), (.leaf 4 (Common.fact 406).pointIds 406), (.leaf 5 (Common.fact 407).pointIds 407), B0181]
theorem treeEq0090 : B0090.tree = HexagonCover.NBand.M7300_7500.SplitData.node0090 := by
  change Tree.branch (101 : Fin 172) _ = Tree.branch (101 : Fin 172) _
  apply congrArg (Tree.branch (101 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0181

theorem accepted0090 : B0090.accepted = true := by decide +kernel
theorem checked0090 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node0090 (maskNeeds ![385, 618970020002979207150831106, 77937529740219874547716, 79344219392947341994315767816, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0090]
  exact B0090.sound accepted0090
#print axioms checked0090

def B0216 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692015886240373161957371353695048238292648689680, 393248, 397528445375783665234659403553046924245505110704192] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 607).pointIds 607), (.leaf 5 (Common.fact 197).pointIds 197), (.leaf 6 (Common.fact 608).pointIds 608)]
theorem treeEq0216 : B0216.tree = HexagonCover.NBand.M7300_7500.SplitData.node0216 := by
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
  · rfl

def B0215 : Block := .branch 163 ![385, 1538, 6148, 24584, 2787593149816327892691964784081045188345872, 393248, 397528445375783665234659403553046924245505110704192] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B0216, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 606).pointIds 606)]
theorem treeEq0215 : B0215.tree = HexagonCover.NBand.M7300_7500.SplitData.node0215 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0216
  · rfl
  · rfl

def B0214 : Block := .branch 168 ![748288838313464829416151751658669827889766433030529, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 716411439502796268421834949508828613379719184, 393248, 23384026219072518174516086377678471213586379702336] ![(.leaf 0 (Common.fact 605).pointIds 605), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B0215]
theorem treeEq0214 : B0214.tree = HexagonCover.NBand.M7300_7500.SplitData.node0214 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0215

def B0213 : Block := .branch 125 ![748288838313422294120286634350736906063837462004097, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 716411439502796268421834949508828613379719184, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516395862688292558655104483392] ![B0214, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq0213 : B0213.tree = HexagonCover.NBand.M7300_7500.SplitData.node0213 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0214
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0212 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 716411439502796268421834949508828613379719184, 1496577676626844588240573268701473812127674924400672, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0213]
theorem treeEq0212 : B0212.tree = HexagonCover.NBand.M7300_7500.SplitData.node0212 := by
  change Tree.branch (164 : Fin 172) _ = Tree.branch (164 : Fin 172) _
  apply congrArg (Tree.branch (164 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0213

def B0211 : Block := .branch 169 ![385, 302231815192726994945538, 77937529740219874547716, 116056878683004400771817480, 717456786933977391381594436302859005325312016, 1496577676626844588240573268701473812127674924400672, 21778071483258057509247406934297633357888] ![B0212, (.leaf 1 (Common.fact 601).pointIds 601), (.leaf 2 (Common.fact 499).pointIds 499), (.leaf 3 (Common.fact 500).pointIds 500), (.leaf 4 (Common.fact 602).pointIds 602), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 603).pointIds 603)]
theorem treeEq0211 : B0211.tree = HexagonCover.NBand.M7300_7500.SplitData.node0211 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0212
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0210 : Block := .branch 170 ![1208925819614629174706561, 302231815192726994945538, 77937529740219874547716, 116056878683004400771817480, 2993156070710476110458537918997383927114355173326864, 393248, 21778071483258057509247406934297633357888] ![(.leaf 0 (Common.fact 596).pointIds 596), (.leaf 1 (Common.fact 597).pointIds 597), (.leaf 2 (Common.fact 463).pointIds 463), (.leaf 3 (Common.fact 598).pointIds 598), (.leaf 4 (Common.fact 599).pointIds 599), B0211, (.leaf 6 (Common.fact 600).pointIds 600)]
theorem treeEq0210 : B0210.tree = HexagonCover.NBand.M7300_7500.SplitData.node0210 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0211
  · rfl

def B0209 : Block := .branch 171 ![1208925819614629174706561, 302231815192726994945538, 77937529740219874547716, 116056878683004400771817480, 717456786933977391381594436302859005325312016, 22300745198530623141535718272648361506373664, 21778071483258057509247406934297633357888] ![(.leaf 0 (Common.fact 592).pointIds 592), (.leaf 1 (Common.fact 593).pointIds 593), (.leaf 2 (Common.fact 547).pointIds 547), (.leaf 3 (Common.fact 557).pointIds 557), B0210, (.leaf 5 (Common.fact 594).pointIds 594), (.leaf 6 (Common.fact 595).pointIds 595)]
theorem treeEq0209 : B0209.tree = HexagonCover.NBand.M7300_7500.SplitData.node0209 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0210
  · rfl
  · rfl

def B0208 : Block := .branch 138 ![1208925819614629174706561, 302231815192726994945538, 77937529740219874547716, 79344219392947341994315767816, 717108337790250350395007940704848874676781072, 22300745198530623141535718272648361506373664, 21778071483258057509247406934297633357888] ![(.leaf 0 (Common.fact 110).pointIds 110), (.leaf 1 (Common.fact 111).pointIds 111), (.leaf 2 (Common.fact 112).pointIds 112), (.leaf 3 (Common.fact 113).pointIds 113), B0209, (.leaf 5 (Common.fact 114).pointIds 114), (.leaf 6 (Common.fact 591).pointIds 591)]
theorem treeEq0208 : B0208.tree = HexagonCover.NBand.M7300_7500.SplitData.node0208 := by
  change Tree.branch (138 : Fin 172) _ = Tree.branch (138 : Fin 172) _
  apply congrArg (Tree.branch (138 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0209
  · rfl
  · rfl

def B0207 : Block := .branch 139 ![1208925819614629174706561, 302231815192726994945538, 77937529740219874547716, 79344219392947341994315767816, 716411439502796268421834949508828613379719184, 22300745198530623141535718272648361506373664, 21778071483258057509247406934297633357888] ![(.leaf 0 (Common.fact 104).pointIds 104), (.leaf 1 (Common.fact 105).pointIds 105), (.leaf 2 (Common.fact 106).pointIds 106), (.leaf 3 (Common.fact 107).pointIds 107), B0208, (.leaf 5 (Common.fact 108).pointIds 108), (.leaf 6 (Common.fact 590).pointIds 590)]
theorem treeEq0207 : B0207.tree = HexagonCover.NBand.M7300_7500.SplitData.node0207 := by
  change Tree.branch (139 : Fin 172) _ = Tree.branch (139 : Fin 172) _
  apply congrArg (Tree.branch (139 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0208
  · rfl
  · rfl

def B0206 : Block := .branch 140 ![1208925819614629174706561, 302231815192726994945538, 77937529740219874547716, 79344219392947341994315767816, 716411439502796268421834949508828613379719184, 22300745198530623141535718272648361506373664, 21778071483258057509247406934297633357888] ![(.leaf 0 (Common.fact 98).pointIds 98), (.leaf 1 (Common.fact 99).pointIds 99), (.leaf 2 (Common.fact 100).pointIds 100), (.leaf 3 (Common.fact 101).pointIds 101), B0207, (.leaf 5 (Common.fact 102).pointIds 102), (.leaf 6 (Common.fact 589).pointIds 589)]
theorem treeEq0206 : B0206.tree = HexagonCover.NBand.M7300_7500.SplitData.node0206 := by
  change Tree.branch (140 : Fin 172) _ = Tree.branch (140 : Fin 172) _
  apply congrArg (Tree.branch (140 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0207
  · rfl
  · rfl

def B0205 : Block := .branch 141 ![1208925819614629174706561, 302231815192726994945538, 77937529740219874547716, 79344219392947341994315767816, 713623846352979940529142984724747568191471632, 22300745198530623141535718272648361506373664, 21778071483258057509247406934297633357888] ![(.leaf 0 (Common.fact 92).pointIds 92), (.leaf 1 (Common.fact 93).pointIds 93), (.leaf 2 (Common.fact 94).pointIds 94), (.leaf 3 (Common.fact 95).pointIds 95), B0206, (.leaf 5 (Common.fact 96).pointIds 96), (.leaf 6 (Common.fact 588).pointIds 588)]
theorem treeEq0205 : B0205.tree = HexagonCover.NBand.M7300_7500.SplitData.node0205 := by
  change Tree.branch (141 : Fin 172) _ = Tree.branch (141 : Fin 172) _
  apply congrArg (Tree.branch (141 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0206
  · rfl
  · rfl

def B0204 : Block := .branch 144 ![1208925819614629174706561, 302231815192726994945538, 77937529740219874547716, 79344219392947341994315767816, 713623846352979940529142984724747568191471632, 393248, 21778071483258057509247406934297633357888] ![(.leaf 0 (Common.fact 128).pointIds 128), (.leaf 1 (Common.fact 129).pointIds 129), (.leaf 2 (Common.fact 130).pointIds 130), (.leaf 3 (Common.fact 131).pointIds 131), (.leaf 4 (Common.fact 132).pointIds 132), B0205, (.leaf 6 (Common.fact 133).pointIds 133)]
theorem treeEq0204 : B0204.tree = HexagonCover.NBand.M7300_7500.SplitData.node0204 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0205
  · rfl

theorem accepted0204 : B0204.accepted = true := by decide +kernel
theorem checked0204 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node0204 (maskNeeds ![1208925819614629174706561, 302231815192726994945538, 77937529740219874547716, 79344219392947341994315767816, 713623846352979940529142984724747568191471632, 393248, 21778071483258057509247406934297633357888]) := by
  rw [← treeEq0204]
  exact B0204.sound accepted0204
#print axioms checked0204

end HexagonCover.NBand.M7300_7500.SplitTree.Run0001
