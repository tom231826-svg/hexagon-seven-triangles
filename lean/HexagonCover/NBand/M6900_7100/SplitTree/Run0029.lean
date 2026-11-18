import HexagonCover.NBand.M6900_7100.SplitData
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6900_7100.SplitTree.Run0029
open OwnerTree HexagonCover.NBand.M6900_7100

abbrev Block := Chunk (n := 173) (Certificate := Fin 1199) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def B2201 : Block := .branch 118 ![385, 1538, 6148, 5986310706507378352962293152179508887088401699856392, 185542200051774784537577176028434367729757159440, 393248, 1496577676648622660048032348249071245804616952578112] ![(.leaf 0 (Common.fact 281).pointIds 281), (.leaf 1 (Common.fact 282).pointIds 282), (.leaf 2 (Common.fact 283).pointIds 283), (.leaf 3 (Common.fact 847).pointIds 847), (.leaf 4 (Common.fact 848).pointIds 848), (.leaf 5 (Common.fact 285).pointIds 285), (.leaf 6 (Common.fact 849).pointIds 849)]
theorem treeEq2201 : B2201.tree = HexagonCover.NBand.M6900_7100.SplitData.node2201 := by
  change Tree.branch (118 : Fin 173) _ = Tree.branch (118 : Fin 173) _
  apply congrArg (Tree.branch (118 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2200 : Block := .branch 172 ![748288838313422304507415652620848621927823526855041, 618970019642691236961191426, 89724963174523259066372, 77373613638577702003826696, 186969447744480744418635461997883862866139906064, 42535295865117307932921825928971419680, 1496577676648622660048032348249071245804616952578112] ![(.leaf 0 (Common.fact 842).pointIds 842), (.leaf 1 (Common.fact 843).pointIds 843), (.leaf 2 (Common.fact 844).pointIds 844), B2201, (.leaf 4 (Common.fact 845).pointIds 845), (.leaf 5 (Common.fact 819).pointIds 819), (.leaf 6 (Common.fact 846).pointIds 846)]
theorem treeEq2200 : B2200.tree = HexagonCover.NBand.M6900_7100.SplitData.node2200 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2201
  · rfl
  · rfl
  · rfl

def B2199 : Block := .branch 170 ![748288838313422304507415652620848621927823526855041, 618970167288701420675532290, 89761856662670678169604, 116059239866245835594424328, 186969447744480744418635461997883862866139906064, 42535295865117307932921825928971419680, 21778071807459079547597433676942028570688] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 838).pointIds 838), (.leaf 2 (Common.fact 839).pointIds 839), (.leaf 3 (Common.fact 840).pointIds 840), (.leaf 4 (Common.fact 841).pointIds 841), (.leaf 5 (Common.fact 660).pointIds 660), B2200]
theorem treeEq2199 : B2199.tree = HexagonCover.NBand.M6900_7100.SplitData.node2199 := by
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
  · exact treeEq2200

def B2198 : Block := .branch 151 ![748288838313422304507415652620848621927823526855041, 618970167288701420675532290, 89761856662670678169604, 116059239866245835594424328, 184114952359068824656518890058984872593374412816, 2993155353253731711777011654710880546081278819434528, 21778071807459079547597433676942028570688] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), B2199, (.leaf 5 (Common.fact 791).pointIds 791), (.leaf 6 (Common.fact 836).pointIds 836)]
theorem treeEq2198 : B2198.tree = HexagonCover.NBand.M6900_7100.SplitData.node2198 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2199
  · rfl
  · rfl

def B2197 : Block := .branch 132 ![748288838313422304507415652620848621927823526855041, 618970167288701420675532290, 89761856662670678169604, 116059239866245835594424328, 184114952359068824656518890058984872593374412816, 2993155353253731711777011654710880546081278819434528, 21778071807459079547597433676942028570688] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 220).pointIds 220), (.leaf 5 (Common.fact 221).pointIds 221), B2198]
theorem treeEq2197 : B2197.tree = HexagonCover.NBand.M6900_7100.SplitData.node2197 := by
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
  · exact treeEq2198

def B2196 : Block := .branch 133 ![748288838313422304507415652620848621927823526855041, 618970167288701420675532290, 89761856662670678169604, 116059239866245835594424328, 184114952359068824656518890058984872593374412816, 2993155353253731711777011654710880546081278819434528, 21778071807459079547597433676942028570688] ![(.leaf 0 (Common.fact 210).pointIds 210), (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), (.leaf 4 (Common.fact 214).pointIds 214), (.leaf 5 (Common.fact 215).pointIds 215), B2197]
theorem treeEq2196 : B2196.tree = HexagonCover.NBand.M6900_7100.SplitData.node2196 := by
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
  · exact treeEq2197

def B2195 : Block := .branch 157 ![748288838313422304507415652620848621927823526855041, 618970167288701420675532290, 89761856662670678169604, 116059239866245835594424328, 1427247692705959881058285969449495136382844944, 2993155353253731711777011654710880546081278819434528, 21778071807459079547597433676942028570688] ![(.leaf 0 (Common.fact 205).pointIds 205), (.leaf 1 (Common.fact 206).pointIds 206), (.leaf 2 (Common.fact 207).pointIds 207), (.leaf 3 (Common.fact 208).pointIds 208), B2196, (.leaf 5 (Common.fact 802).pointIds 802), (.leaf 0 [] 0)]
theorem treeEq2195 : B2195.tree = HexagonCover.NBand.M6900_7100.SplitData.node2195 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2196
  · rfl
  · rfl

def B2194 : Block := .branch 171 ![748288838313422304507415652620848621927823526855041, 618970167288701420675532290, 89761856662670678169604, 116059239866245835594424328, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21778071807459079547597433676942028570688] ![(.leaf 0 (Common.fact 830).pointIds 830), (.leaf 1 (Common.fact 831).pointIds 831), (.leaf 2 (Common.fact 832).pointIds 832), (.leaf 3 (Common.fact 833).pointIds 833), (.leaf 4 (Common.fact 834).pointIds 834), B2195, (.leaf 6 (Common.fact 835).pointIds 835)]
theorem treeEq2194 : B2194.tree = HexagonCover.NBand.M6900_7100.SplitData.node2194 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2195
  · rfl

def B2193 : Block := .branch 113 ![748288838313422294122821935551193364866830868414849, 618970167288701420675532290, 89761856662670678169604, 116059239866245835594424328, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21778071807459079547597433676942028570688] ![B2194, (.leaf 1 (Common.fact 253).pointIds 253), (.leaf 2 (Common.fact 254).pointIds 254), (.leaf 3 (Common.fact 255).pointIds 255), (.leaf 4 (Common.fact 256).pointIds 256), (.leaf 5 (Common.fact 257).pointIds 257), (.leaf 6 (Common.fact 829).pointIds 829)]
theorem treeEq2193 : B2193.tree = HexagonCover.NBand.M6900_7100.SplitData.node2193 := by
  change Tree.branch (113 : Fin 173) _ = Tree.branch (113 : Fin 173) _
  apply congrArg (Tree.branch (113 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2194
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2192 : Block := .branch 150 ![748288838313422294122821935551193364866830868414849, 618970167288701420675532290, 89761856662670678169604, 116059239866245835594424328, 98320, 42535295865117307932921825928971419680, 21778071807775992197654491027316204372032] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), B2193, (.leaf 5 (Common.fact 191).pointIds 191), (.leaf 6 (Common.fact 192).pointIds 192)]
theorem treeEq2192 : B2192.tree = HexagonCover.NBand.M6900_7100.SplitData.node2192 := by
  change Tree.branch (150 : Fin 173) _ = Tree.branch (150 : Fin 173) _
  apply congrArg (Tree.branch (150 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2193
  · rfl
  · rfl

def B2191 : Block := .branch 125 ![748288838313422294122821935551193364866830868414849, 618970167288701420675532290, 89761856662670678169604, 116059239866245835594424328, 98320, 393248, 21778071807775992197654491027316204372032] ![(.leaf 0 (Common.fact 770).pointIds 770), (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), B2192, (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq2191 : B2191.tree = HexagonCover.NBand.M6900_7100.SplitData.node2191 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2192
  · rfl

def B2190 : Block := .branch 169 ![2535301200456458802993406411137, 618970168153392549130667522, 89780339435541406685188, 116059239866245835594424328, 713623846352979940529142984724747568191471632, 393248, 21778071807775992197654491027316204372032] ![B2191, (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 828).pointIds 828)]
theorem treeEq2190 : B2190.tree = HexagonCover.NBand.M6900_7100.SplitData.node2190 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2191
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted2190 : B2190.accepted = true := by decide +kernel
theorem checked2190 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node2190 (maskNeeds ![2535301200456458802993406411137, 618970168153392549130667522, 89780339435541406685188, 116059239866245835594424328, 713623846352979940529142984724747568191471632, 393248, 21778071807775992197654491027316204372032]) := by
  rw [← treeEq2190]
  exact B2190.sound accepted2190
#print axioms checked2190

def B2215 : Block := .branch 172 ![748288838313422294120286634955199815871152049357185, 1461501637330902918204303802735925710892893734402, 374144419156711147060143317255648683240702699640836, 174224571863520570666861437582767328092168, 17539446895663540978325276278564845731007573360656, 42535295865117307932921825928971419680, 16747358238031692654545439388446389205205056] ![(.leaf 0 (Common.fact 859).pointIds 859), (.leaf 1 (Common.fact 804).pointIds 804), (.leaf 2 (Common.fact 805).pointIds 805), (.leaf 3 (Common.fact 806).pointIds 806), (.leaf 4 (Common.fact 818).pointIds 818), (.leaf 5 (Common.fact 819).pointIds 819), (.leaf 6 (Common.fact 860).pointIds 860)]
theorem treeEq2215 : B2215.tree = HexagonCover.NBand.M6900_7100.SplitData.node2215 := by
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
  · rfl

def B2214 : Block := .branch 124 ![748288838313422294120286634955199815871152049357185, 1461501637330902918204303802735925710892893734402, 374144419156711147060143317255648683240702699640836, 174224571863520570666861437582767328092168, 17539446895663540978325276278564845731007573360656, 42535295865117307932921825928971419680, 16747336970383760095891472927533424719691840] ![(.leaf 0 (Common.fact 486).pointIds 486), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B2215]
theorem treeEq2214 : B2214.tree = HexagonCover.NBand.M6900_7100.SplitData.node2214 := by
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
  · exact treeEq2215

def B2213 : Block := .branch 79 ![748288838313422294120286634350736906063837462004097, 1461501637330902918204303802735925710892893734402, 374144419156711147060143317255648683240702699640836, 174224571863520570666861437582767328092168, 17539446895663540978325276278564845731007573360656, 42535295865117307932921825928971419680, 16747336970383760095891472927533424719691840] ![B2214, (.leaf 1 (Common.fact 578).pointIds 578), (.leaf 2 (Common.fact 223).pointIds 223), (.leaf 3 (Common.fact 224).pointIds 224), (.leaf 4 (Common.fact 225).pointIds 225), (.leaf 5 (Common.fact 226).pointIds 226), (.leaf 6 (Common.fact 858).pointIds 858)]
theorem treeEq2213 : B2213.tree = HexagonCover.NBand.M6900_7100.SplitData.node2213 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2214
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2212 : Block := .branch 160 ![748288838313422294120286634350736906063837462004097, 618970019642691236961191426, 374144419156711147060143317255648683240702699640836, 174224571863520570666861437582767328092168, 17539446895663540978325276278564845731007573360656, 42535295865117307932921825928971419680, 16747336970383760095891472927533424719691840] ![(.leaf 0 (Common.fact 299).pointIds 299), B2213, (.leaf 2 (Common.fact 777).pointIds 777), (.leaf 3 (Common.fact 301).pointIds 301), (.leaf 4 (Common.fact 302).pointIds 302), (.leaf 5 (Common.fact 303).pointIds 303), (.leaf 6 (Common.fact 857).pointIds 857)]
theorem treeEq2212 : B2212.tree = HexagonCover.NBand.M6900_7100.SplitData.node2212 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2213
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2211 : Block := .branch 168 ![748288838313422294120286634350736906063837462004097, 618970020002979207150831106, 80280230208783968638980, 174224571863520609352487665250900918689800, 17540160519509893958265805421549570478575764733968, 42535295865117307932921825928971419680, 16747336970383760095891472927533424719691840] ![(.leaf 0 (Common.fact 391).pointIds 391), (.leaf 1 (Common.fact 392).pointIds 392), B2212, (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 856).pointIds 856)]
theorem treeEq2211 : B2211.tree = HexagonCover.NBand.M6900_7100.SplitData.node2211 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2212
  · rfl
  · rfl
  · rfl
  · rfl

def B2210 : Block := .branch 143 ![748288838313422294120286634350736906063837462004097, 618970020002979207150831106, 80280230208783968638980, 174224571863520609352487665250900918689800, 1514117837146354482198839074123023382606250688741392, 42535295865117307932921825928971419680, 5596964371118448525123613791209243966701632] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), (.leaf 5 (Common.fact 498).pointIds 498), B2211]
theorem treeEq2210 : B2210.tree = HexagonCover.NBand.M6900_7100.SplitData.node2210 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2211

def B2209 : Block := .branch 162 ![748288838313422294120286634350736906063837462004097, 618970020002979207150831106, 80280230208783968638980, 174224571863520609352487665250900918689800, 1508271830597030870526024334792158250527626958569488, 42535295865117307932921825928971419680, 5596964371118448525123613791209243966701632] ![(.leaf 0 (Common.fact 350).pointIds 350), (.leaf 1 (Common.fact 351).pointIds 351), (.leaf 2 (Common.fact 352).pointIds 352), (.leaf 3 (Common.fact 781).pointIds 781), B2210, (.leaf 5 (Common.fact 353).pointIds 353), (.leaf 6 (Common.fact 855).pointIds 855)]
theorem treeEq2209 : B2209.tree = HexagonCover.NBand.M6900_7100.SplitData.node2209 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2210
  · rfl
  · rfl

def B2208 : Block := .branch 137 ![748288838313422294120286634350736906063837462004097, 618970020002979207150831106, 80280230208783968638980, 116059239866245835594424328, 1508271830597030870526024334792158250527626958569488, 42535295865117307932921825928971419680, 5596964371118448525123613791209243966701632] ![(.leaf 0 (Common.fact 270).pointIds 270), (.leaf 1 (Common.fact 271).pointIds 271), (.leaf 2 (Common.fact 272).pointIds 272), B2209, (.leaf 4 (Common.fact 854).pointIds 854), (.leaf 5 (Common.fact 274).pointIds 274), (.leaf 0 [] 0)]
theorem treeEq2208 : B2208.tree = HexagonCover.NBand.M6900_7100.SplitData.node2208 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2209
  · rfl
  · rfl
  · rfl

def B2207 : Block := .branch 150 ![748288838313422294120286634350736906063837462004097, 618970020002979207150831106, 80280230208783968638980, 116059239866245835594424328, 1508270403349338164566143276506188801032490575822864, 42535295865117307932921825928971419680, 5596964371118448525123613791209243966701632] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), B2208, (.leaf 5 (Common.fact 191).pointIds 191), (.leaf 6 (Common.fact 192).pointIds 192)]
theorem treeEq2207 : B2207.tree = HexagonCover.NBand.M6900_7100.SplitData.node2207 := by
  change Tree.branch (150 : Fin 173) _ = Tree.branch (150 : Fin 173) _
  apply congrArg (Tree.branch (150 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2208
  · rfl
  · rfl

def B2206 : Block := .branch 125 ![748288838313422294120286634350736906063837462004097, 618970020002979207150831106, 80280230208783968638980, 116059239866245835594424328, 1508270403349338164566143276506188801032490575822864, 393248, 5596964371118448525123613791209243966701632] ![(.leaf 0 (Common.fact 853).pointIds 853), (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), B2207, (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq2206 : B2206.tree = HexagonCover.NBand.M6900_7100.SplitData.node2206 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2207
  · rfl

def B2205 : Block := .branch 169 ![385, 618970020579439959454254594, 80298712981654697154564, 116059239866245835594424328, 1508270403349338164566143276506188801032490575822864, 393248, 5596964371118448525123613791209243966701632] ![B2206, (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 852).pointIds 852)]
theorem treeEq2205 : B2205.tree = HexagonCover.NBand.M6900_7100.SplitData.node2205 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2206
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2204 : Block := .branch 142 ![385, 618970020579439959454254594, 80298712981654697154564, 116059239866245835594424328, 1508270403349338164566143276506188801032490575822864, 393248, 21778071485792739739684223047153590206528] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), (.leaf 4 (Common.fact 612).pointIds 612), (.leaf 5 (Common.fact 156).pointIds 156), B2205]
theorem treeEq2204 : B2204.tree = HexagonCover.NBand.M6900_7100.SplitData.node2204 := by
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
  · exact treeEq2205

def B2203 : Block := .branch 163 ![385, 618970020579439959454254594, 80298712981654697154564, 116059239866245835594424328, 1496578390250690941220513797844458536875243115479056, 393248, 21778071485792739739684223047153590206528] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), B2204, (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 851).pointIds 851)]
theorem treeEq2203 : B2203.tree = HexagonCover.NBand.M6900_7100.SplitData.node2203 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2204
  · rfl
  · rfl

def B2202 : Block := .branch 170 ![385, 618970168153392549130667522, 80335606469802116257796, 116059239866245835594424328, 713623846352979940529142984724747568191471632, 393248, 21778071485792739739684223047153590206528] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 838).pointIds 838), (.leaf 2 (Common.fact 839).pointIds 839), (.leaf 3 (Common.fact 840).pointIds 840), B2203, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 850).pointIds 850)]
theorem treeEq2202 : B2202.tree = HexagonCover.NBand.M6900_7100.SplitData.node2202 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2203
  · rfl
  · rfl

theorem accepted2202 : B2202.accepted = true := by decide +kernel
theorem checked2202 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node2202 (maskNeeds ![385, 618970168153392549130667522, 80335606469802116257796, 116059239866245835594424328, 713623846352979940529142984724747568191471632, 393248, 21778071485792739739684223047153590206528]) := by
  rw [← treeEq2202]
  exact B2202.sound accepted2202
#print axioms checked2202

def B2229 : Block := .branch 172 ![748288838313422294120286634955199815871152049357185, 1461501637330902918204303802735925710892893734402, 374144419156711147060143317255648683240702699640836, 174224571863520570666861437582767328092168, 17539446895663540978325276278564845731007573360656, 42535295865117307932921825928971419680, 16747358238029159519740051679058876872261696] ![(.leaf 0 (Common.fact 859).pointIds 859), (.leaf 1 (Common.fact 804).pointIds 804), (.leaf 2 (Common.fact 805).pointIds 805), (.leaf 3 (Common.fact 806).pointIds 806), (.leaf 4 (Common.fact 818).pointIds 818), (.leaf 5 (Common.fact 819).pointIds 819), (.leaf 6 (Common.fact 868).pointIds 868)]
theorem treeEq2229 : B2229.tree = HexagonCover.NBand.M6900_7100.SplitData.node2229 := by
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
  · rfl

def B2228 : Block := .branch 124 ![748288838313422294120286634955199815871152049357185, 1461501637330902918204303802735925710892893734402, 374144419156711147060143317255648683240702699640836, 174224571863520570666861437582767328092168, 17539446895663540978325276278564845731007573360656, 42535295865117307932921825928971419680, 16747336970381226961086085218145912386748480] ![(.leaf 0 (Common.fact 486).pointIds 486), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B2229]
theorem treeEq2228 : B2228.tree = HexagonCover.NBand.M6900_7100.SplitData.node2228 := by
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
  · exact treeEq2229

def B2227 : Block := .branch 79 ![748288838313422294120286634350736906063837462004097, 1461501637330902918204303802735925710892893734402, 374144419156711147060143317255648683240702699640836, 174224571863520570666861437582767328092168, 17539446895663540978325276278564845731007573360656, 42535295865117307932921825928971419680, 16747336970381226961086085218145912386748480] ![B2228, (.leaf 1 (Common.fact 578).pointIds 578), (.leaf 2 (Common.fact 223).pointIds 223), (.leaf 3 (Common.fact 224).pointIds 224), (.leaf 4 (Common.fact 225).pointIds 225), (.leaf 5 (Common.fact 226).pointIds 226), (.leaf 6 (Common.fact 867).pointIds 867)]
theorem treeEq2227 : B2227.tree = HexagonCover.NBand.M6900_7100.SplitData.node2227 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2228
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2226 : Block := .branch 160 ![748288838313422294120286634350736906063837462004097, 618970019642691236961191426, 374144419156711147060143317255648683240702699640836, 174224571863520570666861437582767328092168, 17539446895663540978325276278564845731007573360656, 42535295865117307932921825928971419680, 16747336970381226961086085218145912386748480] ![(.leaf 0 (Common.fact 299).pointIds 299), B2227, (.leaf 2 (Common.fact 777).pointIds 777), (.leaf 3 (Common.fact 301).pointIds 301), (.leaf 4 (Common.fact 302).pointIds 302), (.leaf 5 (Common.fact 303).pointIds 303), (.leaf 6 (Common.fact 866).pointIds 866)]
theorem treeEq2226 : B2226.tree = HexagonCover.NBand.M6900_7100.SplitData.node2226 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2227
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2225 : Block := .branch 168 ![748288838313422294120286634350736906063837462004097, 618970020002979207150831106, 80280230208783968638980, 174224571863520609352487665250900918689800, 17540160519509893958265805421549570478575764733968, 42535295865117307932921825928971419680, 16747336970381226961086085218145912386748480] ![(.leaf 0 (Common.fact 391).pointIds 391), (.leaf 1 (Common.fact 392).pointIds 392), B2226, (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 865).pointIds 865)]
theorem treeEq2225 : B2225.tree = HexagonCover.NBand.M6900_7100.SplitData.node2225 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2226
  · rfl
  · rfl
  · rfl
  · rfl

def B2224 : Block := .branch 143 ![748288838313422294120286634350736906063837462004097, 618970020002979207150831106, 80280230208783968638980, 174224571863520609352487665250900918689800, 1514117837146354482198839074123023382606250688741392, 42535295865117307932921825928971419680, 5596964371115915390318226081821731633758272] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), (.leaf 5 (Common.fact 498).pointIds 498), B2225]
theorem treeEq2224 : B2224.tree = HexagonCover.NBand.M6900_7100.SplitData.node2224 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2225

def B2223 : Block := .branch 162 ![748288838313422294120286634350736906063837462004097, 618970020002979207150831106, 80280230208783968638980, 174224571863520609352487665250900918689800, 1508271830597030870526024334792158250527626958569488, 42535295865117307932921825928971419680, 5596964371115915390318226081821731633758272] ![(.leaf 0 (Common.fact 350).pointIds 350), (.leaf 1 (Common.fact 351).pointIds 351), (.leaf 2 (Common.fact 352).pointIds 352), (.leaf 3 (Common.fact 781).pointIds 781), B2224, (.leaf 5 (Common.fact 353).pointIds 353), (.leaf 6 (Common.fact 864).pointIds 864)]
theorem treeEq2223 : B2223.tree = HexagonCover.NBand.M6900_7100.SplitData.node2223 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2224
  · rfl
  · rfl

def B2222 : Block := .branch 137 ![748288838313422294120286634350736906063837462004097, 618970020002979207150831106, 80280230208783968638980, 116059239866245835594424328, 1508271830597030870526024334792158250527626958569488, 42535295865117307932921825928971419680, 5596964371115915390318226081821731633758272] ![(.leaf 0 (Common.fact 270).pointIds 270), (.leaf 1 (Common.fact 271).pointIds 271), (.leaf 2 (Common.fact 272).pointIds 272), B2223, (.leaf 4 (Common.fact 854).pointIds 854), (.leaf 5 (Common.fact 274).pointIds 274), (.leaf 0 [] 0)]
theorem treeEq2222 : B2222.tree = HexagonCover.NBand.M6900_7100.SplitData.node2222 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2223
  · rfl
  · rfl
  · rfl

def B2221 : Block := .branch 150 ![748288838313422294120286634350736906063837462004097, 618970020002979207150831106, 80280230208783968638980, 116059239866245835594424328, 1508270403349338164566143276506188801032490575822864, 42535295865117307932921825928971419680, 5596964371115915699803235903166800358539328] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), B2222, (.leaf 5 (Common.fact 191).pointIds 191), (.leaf 6 (Common.fact 192).pointIds 192)]
theorem treeEq2221 : B2221.tree = HexagonCover.NBand.M6900_7100.SplitData.node2221 := by
  change Tree.branch (150 : Fin 173) _ = Tree.branch (150 : Fin 173) _
  apply congrArg (Tree.branch (150 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2222
  · rfl
  · rfl

def B2220 : Block := .branch 125 ![748288838313422294120286634350736906063837462004097, 618970020002979207150831106, 80280230208783968638980, 116059239866245835594424328, 1508270403349338164566143276506188801032490575822864, 393248, 5596964371115915699803235903166800358539328] ![(.leaf 0 (Common.fact 853).pointIds 853), (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), B2221, (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq2220 : B2220.tree = HexagonCover.NBand.M6900_7100.SplitData.node2220 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2221
  · rfl

def B2219 : Block := .branch 169 ![385, 618970020579439959454254594, 80298712981654697154564, 116059239866245835594424328, 1508270403349338164566143276506188801032490575822864, 393248, 5596964371115915699803235903166800358539328] ![B2220, (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 863).pointIds 863)]
theorem treeEq2219 : B2219.tree = HexagonCover.NBand.M6900_7100.SplitData.node2219 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2220
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2218 : Block := .branch 142 ![385, 618970020579439959454254594, 80298712981654697154564, 116059239866245835594424328, 1508270403349338164566143276506188801032490575822864, 393248, 21778071483259914419306335004709982044224] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), (.leaf 4 (Common.fact 612).pointIds 612), (.leaf 5 (Common.fact 156).pointIds 156), B2219]
theorem treeEq2218 : B2218.tree = HexagonCover.NBand.M6900_7100.SplitData.node2218 := by
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
  · exact treeEq2219

def B2217 : Block := .branch 163 ![385, 618970020579439959454254594, 80298712981654697154564, 116059239866245835594424328, 1496578390250690941220513797844458536875243115479056, 393248, 21778071483259914419306335004709982044224] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), B2218, (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 862).pointIds 862)]
theorem treeEq2217 : B2217.tree = HexagonCover.NBand.M6900_7100.SplitData.node2217 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2218
  · rfl
  · rfl

def B2216 : Block := .branch 170 ![385, 618970168153392549130667522, 80335606469802116257796, 116059239866245835594424328, 713623846352979940529142984724747568191471632, 393248, 21778071483259914419306335004709982044224] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 838).pointIds 838), (.leaf 2 (Common.fact 839).pointIds 839), (.leaf 3 (Common.fact 840).pointIds 840), B2217, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 861).pointIds 861)]
theorem treeEq2216 : B2216.tree = HexagonCover.NBand.M6900_7100.SplitData.node2216 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2217
  · rfl
  · rfl

theorem accepted2216 : B2216.accepted = true := by decide +kernel
theorem checked2216 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node2216 (maskNeeds ![385, 618970168153392549130667522, 80335606469802116257796, 116059239866245835594424328, 713623846352979940529142984724747568191471632, 393248, 21778071483259914419306335004709982044224]) := by
  rw [← treeEq2216]
  exact B2216.sound accepted2216
#print axioms checked2216

def B2240 : Block := .branch 163 ![385, 1538, 6148, 24584, 2961817722004366939643639309869266533187600, 393248, 5596964371115913533408167153751319285071936] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), (.leaf 4 (Common.fact 876).pointIds 876), (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 877).pointIds 877)]
theorem treeEq2240 : B2240.tree = HexagonCover.NBand.M6900_7100.SplitData.node2240 := by
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
  · rfl

def B2239 : Block := .branch 137 ![385, 1538, 6148, 5986310706507378352962293152179508887088401699856392, 2787593150140846446350391510864201208922128, 393248, 5596964371115913533408167153751319285071936] ![(.leaf 0 (Common.fact 270).pointIds 270), (.leaf 1 (Common.fact 271).pointIds 271), (.leaf 2 (Common.fact 272).pointIds 272), (.leaf 3 (Common.fact 806).pointIds 806), B2240, (.leaf 5 (Common.fact 274).pointIds 274), (.leaf 0 [] 0)]
theorem treeEq2239 : B2239.tree = HexagonCover.NBand.M6900_7100.SplitData.node2239 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2240
  · rfl
  · rfl

def B2238 : Block := .branch 172 ![1208925819614629174706561, 302231526962350843233794, 89724963174523259066372, 77373613638577702003826696, 1496577679762886882108460701638360921002006781460496, 22300745198530623141535718272648361506373664, 5596964371115913533408167153751319285071936] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 872).pointIds 872), (.leaf 2 (Common.fact 844).pointIds 844), B2239, (.leaf 4 (Common.fact 873).pointIds 873), (.leaf 5 (Common.fact 874).pointIds 874), (.leaf 6 (Common.fact 875).pointIds 875)]
theorem treeEq2238 : B2238.tree = HexagonCover.NBand.M6900_7100.SplitData.node2238 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2239
  · rfl
  · rfl
  · rfl

def B2237 : Block := .branch 142 ![1208925819614629174706561, 302231526962350843233794, 89724963174523259066372, 77373613638577702003826696, 1496577679762886882108460701638360921002006781460496, 22300745198530623141535718272648361506373664, 21778071483257748024237585589228908576832] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 156).pointIds 156), B2238]
theorem treeEq2237 : B2237.tree = HexagonCover.NBand.M6900_7100.SplitData.node2237 := by
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
  · exact treeEq2238

def B2243 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496577676626844588240573268701473812127674924105744, 2993155353253689176481146537402947624255349848408096, 21778071807459389032607255022010753351744] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), (.leaf 5 (Common.fact 883).pointIds 883), (.leaf 6 (Common.fact 884).pointIds 884)]
theorem treeEq2243 : B2243.tree = HexagonCover.NBand.M6900_7100.SplitData.node2243 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2242 : Block := .branch 171 ![748288838313422294122821935551193364866830868414849, 302231526962350843233794, 89724963174523259066372, 77373613638577702003826696, 1496577679762886881783942147979934194218850760884240, 393248, 21778071807459389032607255022010753351744] ![(.leaf 0 (Common.fact 879).pointIds 879), (.leaf 1 (Common.fact 880).pointIds 880), (.leaf 2 (Common.fact 832).pointIds 832), (.leaf 3 (Common.fact 833).pointIds 833), (.leaf 4 (Common.fact 881).pointIds 881), B2243, (.leaf 6 (Common.fact 882).pointIds 882)]
theorem treeEq2242 : B2242.tree = HexagonCover.NBand.M6900_7100.SplitData.node2242 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2243
  · rfl

def B2241 : Block := .branch 169 ![2535301200456458802993406411137, 302232391653479298369026, 89743445947393987581956, 116059239866245835594424328, 1496578393386733234763882677122918918966418952257552, 393248, 21778071807459389032607255022010753351744] ![B2242, (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 878).pointIds 878)]
theorem treeEq2241 : B2241.tree = HexagonCover.NBand.M6900_7100.SplitData.node2241 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2242
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2236 : Block := .branch 108 ![2535302409382278417622581117313, 302232391653479298369026, 89743445947393987581956, 116059239866245835594424328, 1496578393386733234763882677122918918966418952257552, 22300745198530623141535718272648361506373664, 21778071483257748024237585589228908576832] ![(.leaf 0 (Common.fact 318).pointIds 318), (.leaf 1 (Common.fact 319).pointIds 319), (.leaf 2 (Common.fact 320).pointIds 320), (.leaf 3 (Common.fact 321).pointIds 321), B2237, (.leaf 5 (Common.fact 322).pointIds 322), B2241]
theorem treeEq2236 : B2236.tree = HexagonCover.NBand.M6900_7100.SplitData.node2236 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2237
  · rfl
  · exact treeEq2241

def B2247 : Block := .branch 118 ![385, 1538, 6148, 5986310706507378352962293152179508887088401699856392, 11692015886240373161957371353695048238292648689680, 393248, 21778071485793049224694044392222314987584] ![(.leaf 0 (Common.fact 281).pointIds 281), (.leaf 1 (Common.fact 282).pointIds 282), (.leaf 2 (Common.fact 283).pointIds 283), (.leaf 3 (Common.fact 847).pointIds 847), (.leaf 4 (Common.fact 888).pointIds 888), (.leaf 5 (Common.fact 285).pointIds 285), (.leaf 6 (Common.fact 889).pointIds 889)]
theorem treeEq2247 : B2247.tree = HexagonCover.NBand.M6900_7100.SplitData.node2247 := by
  change Tree.branch (118 : Fin 173) _ = Tree.branch (118 : Fin 173) _
  apply congrArg (Tree.branch (118 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2246 : Block := .branch 172 ![1208925819614629174706561, 302231526962350843233794, 89724963174523259066372, 77373613638577702003826696, 1508269692861534105129571626641664458376098221228048, 22300745198530623141535718272648361506373664, 5596964371118448834608623612554312691482688] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 872).pointIds 872), (.leaf 2 (Common.fact 844).pointIds 844), B2247, (.leaf 4 (Common.fact 873).pointIds 873), (.leaf 5 (Common.fact 874).pointIds 874), (.leaf 6 (Common.fact 887).pointIds 887)]
theorem treeEq2246 : B2246.tree = HexagonCover.NBand.M6900_7100.SplitData.node2246 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2247
  · rfl
  · rfl
  · rfl

def B2245 : Block := .branch 142 ![1208925819614629174706561, 302231526962350843233794, 89724963174523259066372, 77373613638577702003826696, 1508269692861534105129571626641664458376098221228048, 22300745198530623141535718272648361506373664, 21778071485793049224694044392222314987584] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), (.leaf 4 (Common.fact 886).pointIds 886), (.leaf 5 (Common.fact 156).pointIds 156), B2246]
theorem treeEq2245 : B2245.tree = HexagonCover.NBand.M6900_7100.SplitData.node2245 := by
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
  · exact treeEq2246

def B2244 : Block := .branch 163 ![1208925819614629174706561, 302231526962350843233794, 89724963174523259066372, 77373613638577702003826696, 1496577679762886881783942147979934194218850760884240, 22300745198530623141535718272648361506373664, 21778071485793049224694044392222314987584] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), B2245, (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 885).pointIds 885)]
theorem treeEq2244 : B2244.tree = HexagonCover.NBand.M6900_7100.SplitData.node2244 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2245
  · rfl
  · rfl

def B2235 : Block := .branch 101 ![1208925819614629174706561, 302232391653479298369026, 89743445947393987581956, 116059239866245835594424328, 1496578393386733234763882677122918918966418952257552, 22300745198530623141535718272648361506373664, 21778071483257748024237585589228908576832] ![B2236, (.leaf 1 (Common.fact 460).pointIds 460), (.leaf 2 (Common.fact 461).pointIds 461), (.leaf 3 (Common.fact 462).pointIds 462), (.leaf 4 (Common.fact 463).pointIds 463), (.leaf 5 (Common.fact 464).pointIds 464), B2244]
theorem treeEq2235 : B2235.tree = HexagonCover.NBand.M6900_7100.SplitData.node2235 := by
  change Tree.branch (101 : Fin 173) _ = Tree.branch (101 : Fin 173) _
  apply congrArg (Tree.branch (101 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2236
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2244

def B2251 : Block := .branch 118 ![385, 1538, 6148, 5986310706507378352962293152179508887088401699856392, 11692015886240373161957371353695048238292648689680, 393248, 21778071483259604934296513659641257263168] ![(.leaf 0 (Common.fact 281).pointIds 281), (.leaf 1 (Common.fact 282).pointIds 282), (.leaf 2 (Common.fact 283).pointIds 283), (.leaf 3 (Common.fact 847).pointIds 847), (.leaf 4 (Common.fact 888).pointIds 888), (.leaf 5 (Common.fact 285).pointIds 285), (.leaf 6 (Common.fact 891).pointIds 891)]
theorem treeEq2251 : B2251.tree = HexagonCover.NBand.M6900_7100.SplitData.node2251 := by
  change Tree.branch (118 : Fin 173) _ = Tree.branch (118 : Fin 173) _
  apply congrArg (Tree.branch (118 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2250 : Block := .branch 172 ![1208925819614629174706561, 302231526962350843233794, 89724963174523259066372, 77373613638577702003826696, 1508269692861534105129571626641664458376098221228048, 22300745198530623141535718272648361506373664, 5596964371115915390318226081821731633758272] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 872).pointIds 872), (.leaf 2 (Common.fact 844).pointIds 844), B2251, (.leaf 4 (Common.fact 873).pointIds 873), (.leaf 5 (Common.fact 874).pointIds 874), (.leaf 6 (Common.fact 890).pointIds 890)]
theorem treeEq2250 : B2250.tree = HexagonCover.NBand.M6900_7100.SplitData.node2250 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2251
  · rfl
  · rfl
  · rfl

def B2249 : Block := .branch 142 ![1208925819614629174706561, 302231526962350843233794, 89724963174523259066372, 77373613638577702003826696, 1508269692861534105129571626641664458376098221228048, 22300745198530623141535718272648361506373664, 21778071483259604934296513659641257263168] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), (.leaf 4 (Common.fact 886).pointIds 886), (.leaf 5 (Common.fact 156).pointIds 156), B2250]
theorem treeEq2249 : B2249.tree = HexagonCover.NBand.M6900_7100.SplitData.node2249 := by
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
  · exact treeEq2250

def B2248 : Block := .branch 163 ![1208925819614629174706561, 302231526962350843233794, 89724963174523259066372, 77373613638577702003826696, 1496577679762886881783942147979934194218850760884240, 22300745198530623141535718272648361506373664, 21778071483259604934296513659641257263168] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), B2249, (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 862).pointIds 862)]
theorem treeEq2248 : B2248.tree = HexagonCover.NBand.M6900_7100.SplitData.node2248 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2249
  · rfl
  · rfl

def B2234 : Block := .branch 91 ![1208925819614629174706561, 302232391653479298369026, 89743445947393987581956, 116059239866245835594424328, 1496578393386733234763882677122918918966418952257552, 22300745198530623141535718272648361506373664, 21778071483257748024237585589228908576832] ![B2235, (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), (.leaf 3 (Common.fact 333).pointIds 333), (.leaf 4 (Common.fact 334).pointIds 334), (.leaf 5 (Common.fact 335).pointIds 335), B2248]
theorem treeEq2234 : B2234.tree = HexagonCover.NBand.M6900_7100.SplitData.node2234 := by
  change Tree.branch (91 : Fin 173) _ = Tree.branch (91 : Fin 173) _
  apply congrArg (Tree.branch (91 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2235
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2248

def B2233 : Block := .branch 138 ![1208925819614629174706561, 302232391653479298369026, 89743445947393987581956, 79344221754130583429138374664, 1496578393038284091036841690536423320956288303726608, 22300745198530623141535718272648361506373664, 21778071483257748024237585589228908576832] ![(.leaf 0 (Common.fact 134).pointIds 134), (.leaf 1 (Common.fact 135).pointIds 135), (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), B2234, (.leaf 5 (Common.fact 138).pointIds 138), (.leaf 6 (Common.fact 139).pointIds 139)]
theorem treeEq2233 : B2233.tree = HexagonCover.NBand.M6900_7100.SplitData.node2233 := by
  change Tree.branch (138 : Fin 173) _ = Tree.branch (138 : Fin 173) _
  apply congrArg (Tree.branch (138 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2234
  · rfl
  · rfl

def B2232 : Block := .branch 141 ![1208925819614629174706561, 302232391653479298369026, 89743445947393987581956, 79344221754130583429138374664, 1496578390250690941220513797844458536875243115479056, 22300745198530623141535718272648361506373664, 21778071483257748024237585589228908576832] ![(.leaf 0 (Common.fact 116).pointIds 116), (.leaf 1 (Common.fact 117).pointIds 117), (.leaf 2 (Common.fact 118).pointIds 118), (.leaf 3 (Common.fact 119).pointIds 119), B2233, (.leaf 5 (Common.fact 120).pointIds 120), (.leaf 6 (Common.fact 121).pointIds 121)]
theorem treeEq2232 : B2232.tree = HexagonCover.NBand.M6900_7100.SplitData.node2232 := by
  change Tree.branch (141 : Fin 173) _ = Tree.branch (141 : Fin 173) _
  apply congrArg (Tree.branch (141 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2233
  · rfl
  · rfl

theorem accepted2232 : B2232.accepted = true := by decide +kernel
theorem checked2232 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node2232 (maskNeeds ![1208925819614629174706561, 302232391653479298369026, 89743445947393987581956, 79344221754130583429138374664, 1496578390250690941220513797844458536875243115479056, 22300745198530623141535718272648361506373664, 21778071483257748024237585589228908576832]) := by
  rw [← treeEq2232]
  exact B2232.sound accepted2232
#print axioms checked2232

def B2265 : Block := .branch 163 ![385, 1538, 6148, 24584, 2961817722004366939643639309869266533187600, 393248, 5596964371115596233901847819719609203294272] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), (.leaf 4 (Common.fact 876).pointIds 876), (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 910).pointIds 910)]
theorem treeEq2265 : B2265.tree = HexagonCover.NBand.M6900_7100.SplitData.node2265 := by
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
  · rfl

def B2264 : Block := .branch 137 ![385, 1538, 6148, 5986310706507378352962293113493882659420268109258760, 2787593150140846446350391510864201208922128, 393248, 5596964371115596233901847819719609203294272] ![(.leaf 0 (Common.fact 270).pointIds 270), (.leaf 1 (Common.fact 271).pointIds 271), (.leaf 2 (Common.fact 272).pointIds 272), (.leaf 3 (Common.fact 909).pointIds 909), B2265, (.leaf 5 (Common.fact 274).pointIds 274), (.leaf 0 [] 0)]
theorem treeEq2264 : B2264.tree = HexagonCover.NBand.M6900_7100.SplitData.node2264 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2265
  · rfl
  · rfl

def B2263 : Block := .branch 172 ![1208925819614629174706561, 302231526962350843233794, 89724963174523259066372, 38687987410909568413229064, 1496577679762886882108460701638360921002006781460496, 43556142965880123323311949751266331459616, 5596964371115596233901847819719609203294272] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 872).pointIds 872), (.leaf 2 (Common.fact 844).pointIds 844), B2264, (.leaf 4 (Common.fact 873).pointIds 873), (.leaf 5 (Common.fact 907).pointIds 907), (.leaf 6 (Common.fact 908).pointIds 908)]
theorem treeEq2263 : B2263.tree = HexagonCover.NBand.M6900_7100.SplitData.node2263 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2264
  · rfl
  · rfl
  · rfl

def B2262 : Block := .branch 142 ![1208925819614629174706561, 302231526962350843233794, 89724963174523259066372, 38687987410909568413229064, 1496577679762886882108460701638360921002006781460496, 43556142965880123323311949751266331459616, 21778071482940448517918251557518826799168] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 156).pointIds 156), B2263]
theorem treeEq2262 : B2262.tree = HexagonCover.NBand.M6900_7100.SplitData.node2262 := by
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
  · exact treeEq2263

def B2268 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496577676626844588240573268701473812127674924105744, 2993155353253689176481146537402947624255349848408096, 21778071807459002176344978340674847375424] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), (.leaf 5 (Common.fact 883).pointIds 883), (.leaf 6 (Common.fact 914).pointIds 914)]
theorem treeEq2268 : B2268.tree = HexagonCover.NBand.M6900_7100.SplitData.node2268 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2267 : Block := .branch 171 ![748288838313422294122821935551193364866830868414849, 302231526962350843233794, 89724963174523259066372, 38687987410909568413229064, 1496577679762886881783942147979934194218850760884240, 393248, 21778071807775914826402035691049023176768] ![(.leaf 0 (Common.fact 879).pointIds 879), (.leaf 1 (Common.fact 880).pointIds 880), (.leaf 2 (Common.fact 832).pointIds 832), (.leaf 3 (Common.fact 912).pointIds 912), (.leaf 4 (Common.fact 881).pointIds 881), B2268, (.leaf 6 (Common.fact 913).pointIds 913)]
theorem treeEq2267 : B2267.tree = HexagonCover.NBand.M6900_7100.SplitData.node2267 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2268
  · rfl

def B2266 : Block := .branch 169 ![2535301200456458802993406411137, 302232391653479298369026, 89743445947393987581956, 38687987410909568413229064, 1496578393386733234763882677122918918966418952257552, 393248, 21778071807775914826402035691049023176768] ![B2267, (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 911).pointIds 911)]
theorem treeEq2266 : B2266.tree = HexagonCover.NBand.M6900_7100.SplitData.node2266 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2267
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2261 : Block := .branch 108 ![2535302409382278417622581117313, 302232391653479298369026, 89743445947393987581956, 38687987410909568413229064, 1496578393386733234763882677122918918966418952257552, 43556142965880123323311949751266331459616, 21778071483257361167975308907893002600512] ![(.leaf 0 (Common.fact 318).pointIds 318), (.leaf 1 (Common.fact 319).pointIds 319), (.leaf 2 (Common.fact 320).pointIds 320), (.leaf 3 (Common.fact 321).pointIds 321), B2262, (.leaf 5 (Common.fact 322).pointIds 322), B2266]
theorem treeEq2261 : B2261.tree = HexagonCover.NBand.M6900_7100.SplitData.node2261 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2262
  · rfl
  · exact treeEq2266

def B2272 : Block := .branch 118 ![385, 1538, 6148, 5986310706507378352962293113493882659420268109258760, 11692015886240373161957371353695048238292648689680, 393248, 21778071485792662368431767710886409011264] ![(.leaf 0 (Common.fact 281).pointIds 281), (.leaf 1 (Common.fact 282).pointIds 282), (.leaf 2 (Common.fact 283).pointIds 283), (.leaf 3 (Common.fact 917).pointIds 917), (.leaf 4 (Common.fact 888).pointIds 888), (.leaf 5 (Common.fact 285).pointIds 285), (.leaf 6 (Common.fact 918).pointIds 918)]
theorem treeEq2272 : B2272.tree = HexagonCover.NBand.M6900_7100.SplitData.node2272 := by
  change Tree.branch (118 : Fin 173) _ = Tree.branch (118 : Fin 173) _
  apply congrArg (Tree.branch (118 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2271 : Block := .branch 172 ![1208925819614629174706561, 302231526962350843233794, 89724963174523259066372, 38687987410909568413229064, 1508269692861534105129571626641664458376098221228048, 43556142965880123323311949751266331459616, 5596964371118448447752361335872976785506368] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 872).pointIds 872), (.leaf 2 (Common.fact 844).pointIds 844), B2272, (.leaf 4 (Common.fact 873).pointIds 873), (.leaf 5 (Common.fact 907).pointIds 907), (.leaf 6 (Common.fact 916).pointIds 916)]
theorem treeEq2271 : B2271.tree = HexagonCover.NBand.M6900_7100.SplitData.node2271 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2272
  · rfl
  · rfl
  · rfl

def B2270 : Block := .branch 142 ![1208925819614629174706561, 302231526962350843233794, 89724963174523259066372, 38687987410909568413229064, 1508269692861534105129571626641664458376098221228048, 43556142965880123323311949751266331459616, 21778071485792662368431767710886409011264] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), (.leaf 4 (Common.fact 886).pointIds 886), (.leaf 5 (Common.fact 156).pointIds 156), B2271]
theorem treeEq2270 : B2270.tree = HexagonCover.NBand.M6900_7100.SplitData.node2270 := by
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
  · exact treeEq2271

def B2269 : Block := .branch 163 ![1208925819614629174706561, 302231526962350843233794, 89724963174523259066372, 38687987410909568413229064, 1496577679762886881783942147979934194218850760884240, 43556142965880123323311949751266331459616, 21778071485792662368431767710886409011264] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), B2270, (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 915).pointIds 915)]
theorem treeEq2269 : B2269.tree = HexagonCover.NBand.M6900_7100.SplitData.node2269 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2270
  · rfl
  · rfl

def B2260 : Block := .branch 101 ![1208925819614629174706561, 302232391653479298369026, 89743445947393987581956, 38687987410909568413229064, 1496578393386733234763882677122918918966418952257552, 43556142965880123323311949751266331459616, 21778071483257361167975308907893002600512] ![B2261, (.leaf 1 (Common.fact 460).pointIds 460), (.leaf 2 (Common.fact 461).pointIds 461), (.leaf 3 (Common.fact 462).pointIds 462), (.leaf 4 (Common.fact 463).pointIds 463), (.leaf 5 (Common.fact 464).pointIds 464), B2269]
theorem treeEq2260 : B2260.tree = HexagonCover.NBand.M6900_7100.SplitData.node2260 := by
  change Tree.branch (101 : Fin 173) _ = Tree.branch (101 : Fin 173) _
  apply congrArg (Tree.branch (101 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2261
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2269

def B2275 : Block := .branch 163 ![385, 1538, 6148, 24584, 1496577679588662309920421654686686395213785436618768, 393248, 21778071483259837048053879668442800848960] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), (.leaf 4 (Common.fact 920).pointIds 920), (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 921).pointIds 921)]
theorem treeEq2275 : B2275.tree = HexagonCover.NBand.M6900_7100.SplitData.node2275 := by
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
  · rfl

def B2274 : Block := .branch 137 ![385, 1538, 6148, 5986310706507378352962293113493882659420268109258760, 1496577679414437738056901161393438596208720112353296, 393248, 21778071483259837048053879668442800848960] ![(.leaf 0 (Common.fact 270).pointIds 270), (.leaf 1 (Common.fact 271).pointIds 271), (.leaf 2 (Common.fact 272).pointIds 272), (.leaf 3 (Common.fact 909).pointIds 909), B2275, (.leaf 5 (Common.fact 274).pointIds 274), (.leaf 0 [] 0)]
theorem treeEq2274 : B2274.tree = HexagonCover.NBand.M6900_7100.SplitData.node2274 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2275
  · rfl
  · rfl

def B2273 : Block := .branch 172 ![1208925819614629174706561, 302231526962350843233794, 89724963174523259066372, 38687987410909568413229064, 1496577679762886881783942147979934194218850760884240, 43556142965880123323311949751266331459616, 21778071483259837048053879668442800848960] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 872).pointIds 872), (.leaf 2 (Common.fact 844).pointIds 844), B2274, (.leaf 4 (Common.fact 873).pointIds 873), (.leaf 5 (Common.fact 907).pointIds 907), (.leaf 6 (Common.fact 919).pointIds 919)]
theorem treeEq2273 : B2273.tree = HexagonCover.NBand.M6900_7100.SplitData.node2273 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2274
  · rfl
  · rfl
  · rfl

def B2259 : Block := .branch 91 ![1208925819614629174706561, 302232391653479298369026, 89743445947393987581956, 38687987410909568413229064, 1496578393386733234763882677122918918966418952257552, 43556142965880123323311949751266331459616, 21778071483257361167975308907893002600512] ![B2260, (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), (.leaf 3 (Common.fact 333).pointIds 333), (.leaf 4 (Common.fact 334).pointIds 334), (.leaf 5 (Common.fact 335).pointIds 335), B2273]
theorem treeEq2259 : B2259.tree = HexagonCover.NBand.M6900_7100.SplitData.node2259 := by
  change Tree.branch (91 : Fin 173) _ = Tree.branch (91 : Fin 173) _
  apply congrArg (Tree.branch (91 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2260
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2273

theorem accepted2259 : B2259.accepted = true := by decide +kernel
theorem checked2259 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node2259 (maskNeeds ![1208925819614629174706561, 302232391653479298369026, 89743445947393987581956, 38687987410909568413229064, 1496578393386733234763882677122918918966418952257552, 43556142965880123323311949751266331459616, 21778071483257361167975308907893002600512]) := by
  rw [← treeEq2259]
  exact B2259.sound accepted2259
#print axioms checked2259

end HexagonCover.NBand.M6900_7100.SplitTree.Run0029
