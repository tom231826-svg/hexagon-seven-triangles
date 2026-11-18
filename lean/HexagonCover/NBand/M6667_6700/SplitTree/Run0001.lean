import HexagonCover.NBand.M6667_6700.SplitData
import HexagonCover.NBand.M6667_6700.SplitTree.Run0000
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6667_6700.SplitTree.Run0001
open OwnerTree HexagonCover.NBand.M6667_6700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1334) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip0033_0038 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0038 ![53171715979825902331119469163985240449, 618970019642691236961191426, 77919046967349146032132, 87112285931760324017876354838799843352584, 1361129792202307512280225212883093520400, 10889035741470030830827987437816583159840, 2793037667688014110285064681869228849496128] HexagonCover.NBand.M6667_6700.SplitTree.Run0000.checked0038
def Tip0033_0082 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0082 ![10636420114708594398197643235014214017, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 1361129792202307512280225212883093520400, 393248, 13611294677154915416106773665797746720832] HexagonCover.NBand.M6667_6700.SplitTree.Run0000.checked0082
def B0079 : Block := .branch 168 ![53171715979825902331119469163985240449, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 88473415723962554158904124715415755653136, 116920130997361269197764817448130629010291186597920, 187072212371393241218085768872748908385188214997056] ![(.leaf 0 (Common.fact 250).pointIds 250), (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 310).pointIds 310), (.leaf 4 (Common.fact 311).pointIds 311), (.leaf 5 (Common.fact 312).pointIds 312), (.leaf 6 (Common.fact 256).pointIds 256)]
theorem treeEq0079 : B0079.tree = HexagonCover.NBand.M6667_6700.SplitData.node0079 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0078 : Block := .branch 167 ![53171715979825902331119469163985240449, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 88473415723962554158904124715415755653136, 116920130997361269197764817448130629010291186597920, 2793037667688014110285064681869228849496128] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 262).pointIds 262), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 308).pointIds 308), (.leaf 5 (Common.fact 309).pointIds 309), B0079]
theorem treeEq0078 : B0078.tree = HexagonCover.NBand.M6667_6700.SplitData.node0078 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0079

def B0077 : Block := .branch 164 ![53171715979825902331119469163985240449, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 88473415723962554158904124715415755653136, 93536104800066822506505860124670100695796265910304, 2793037667688014110285064681869228849496128] ![(.leaf 0 (Common.fact 228).pointIds 228), (.leaf 1 (Common.fact 229).pointIds 229), (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 306).pointIds 306), B0078, (.leaf 0 [] 0)]
theorem treeEq0077 : B0077.tree = HexagonCover.NBand.M6667_6700.SplitData.node0077 := by
  change Tree.branch (164 : Fin 173) _ = Tree.branch (164 : Fin 173) _
  apply congrArg (Tree.branch (164 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0078
  · rfl

def B0076 : Block := .branch 166 ![53171715979825902331119469163985240449, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 88473415723962554158904124715415755653136, 10889035741470030830827987437816583159840, 2793037667688014110285064681869228849496128] ![(.leaf 0 (Common.fact 300).pointIds 300), (.leaf 1 (Common.fact 301).pointIds 301), (.leaf 2 (Common.fact 302).pointIds 302), (.leaf 3 (Common.fact 303).pointIds 303), (.leaf 4 (Common.fact 304).pointIds 304), B0077, (.leaf 6 (Common.fact 305).pointIds 305)]
theorem treeEq0076 : B0076.tree = HexagonCover.NBand.M6667_6700.SplitData.node0076 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0077
  · rfl

def B0037 : Block := .branch 136 ![53171715979825902331119469163985240449, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 1361129792202307512280225212883093520400, 10889035741470030830827987437816583159840, 2793037667688014110285064681869228849496128] ![(.leaf 0 (Common.fact 190).pointIds 190), (.leaf 1 (Common.fact 191).pointIds 191), (.leaf 2 (Common.fact 192).pointIds 192), Tip0033_0038, B0076, (.leaf 5 (Common.fact 193).pointIds 193), (.leaf 0 [] 0)]
theorem treeEq0037 : B0037.tree = HexagonCover.NBand.M6667_6700.SplitData.node0037 := by
  change Tree.branch (136 : Fin 173) _ = Tree.branch (136 : Fin 173) _
  apply congrArg (Tree.branch (136 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0076
  · rfl
  · rfl

def B0081 : Block := .branch 168 ![10636420114708594398197643235014214017, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 1361129792202307512280225212883093520400, 10931571037335148138760909263745554186272, 187072212371393241218085768872748908385188214997056] ![(.leaf 0 (Common.fact 315).pointIds 315), (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 310).pointIds 310), (.leaf 4 (Common.fact 316).pointIds 316), (.leaf 5 (Common.fact 317).pointIds 317), (.leaf 6 (Common.fact 256).pointIds 256)]
theorem treeEq0081 : B0081.tree = HexagonCover.NBand.M6667_6700.SplitData.node0081 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0080 : Block := .branch 167 ![10636420114708594398197643235014214017, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 1361129792202307512280225212883093520400, 10931571037335148138760909263745554186272, 2793037667688014110285064681869228849496128] ![(.leaf 0 (Common.fact 313).pointIds 313), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 262).pointIds 262), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 297).pointIds 297), (.leaf 5 (Common.fact 314).pointIds 314), B0081]
theorem treeEq0080 : B0080.tree = HexagonCover.NBand.M6667_6700.SplitData.node0080 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0081

def B0036 : Block := .branch 125 ![10636420114708594398197643235014214017, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 1361129792202307512280225212883093520400, 10889035741470030830827987437816583159840, 2793037667688014110285064681869228849496128] ![B0037, (.leaf 1 (Common.fact 185).pointIds 185), (.leaf 2 (Common.fact 186).pointIds 186), (.leaf 3 (Common.fact 187).pointIds 187), (.leaf 4 (Common.fact 188).pointIds 188), B0080, (.leaf 6 (Common.fact 189).pointIds 189)]
theorem treeEq0036 : B0036.tree = HexagonCover.NBand.M6667_6700.SplitData.node0036 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0037
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0080
  · rfl

def B0035 : Block := .branch 141 ![10636420114708594398197643235014214017, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 1361129792202307512280225212883093520400, 10889035741470030830827987437816583159840, 5444517871686217593099897788183661248576] ![(.leaf 0 (Common.fact 179).pointIds 179), (.leaf 1 (Common.fact 180).pointIds 180), (.leaf 2 (Common.fact 181).pointIds 181), (.leaf 3 (Common.fact 182).pointIds 182), (.leaf 4 (Common.fact 183).pointIds 183), (.leaf 5 (Common.fact 184).pointIds 184), B0036]
theorem treeEq0035 : B0035.tree = HexagonCover.NBand.M6667_6700.SplitData.node0035 := by
  change Tree.branch (141 : Fin 173) _ = Tree.branch (141 : Fin 173) _
  apply congrArg (Tree.branch (141 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0036

def B0034 : Block := .branch 133 ![10636420114708594398197643235014214017, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 1361129792202307512280225212883093520400, 393248, 8166776807053725300806894647637806940224] ![(.leaf 0 (Common.fact 174).pointIds 174), (.leaf 1 (Common.fact 175).pointIds 175), (.leaf 2 (Common.fact 176).pointIds 176), (.leaf 3 (Common.fact 177).pointIds 177), (.leaf 4 (Common.fact 178).pointIds 178), B0035, Tip0033_0082]
theorem treeEq0034 : B0034.tree = HexagonCover.NBand.M6667_6700.SplitData.node0034 := by
  change Tree.branch (133 : Fin 173) _ = Tree.branch (133 : Fin 173) _
  apply congrArg (Tree.branch (133 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0035
  · rfl

def B0114 : Block := .branch 169 ![10636420114708594398197643235014214017, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 1329552514338574299630590216301019152, 1427247692705959881058285969449495136383139872, 374144419171683571204981831702823814454909188177984] ![(.leaf 0 (Common.fact 362).pointIds 362), (.leaf 1 (Common.fact 363).pointIds 363), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 353).pointIds 353), (.leaf 4 (Common.fact 364).pointIds 364), (.leaf 5 (Common.fact 365).pointIds 365), (.leaf 6 (Common.fact 366).pointIds 366)]
theorem treeEq0114 : B0114.tree = HexagonCover.NBand.M6667_6700.SplitData.node0114 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0113 : Block := .branch 133 ![10636420114708594398197643235014214017, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 1329552514338574299630590216301019152, 187073636826048279489952716873653676011095748640800, 374144419160794535463511800871995827017092605411392] ![(.leaf 0 (Common.fact 174).pointIds 174), (.leaf 1 (Common.fact 175).pointIds 175), (.leaf 2 (Common.fact 176).pointIds 176), (.leaf 3 (Common.fact 177).pointIds 177), (.leaf 4 (Common.fact 178).pointIds 178), (.leaf 5 (Common.fact 361).pointIds 361), B0114]
theorem treeEq0113 : B0113.tree = HexagonCover.NBand.M6667_6700.SplitData.node0113 := by
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
  · exact treeEq0114

def B0112 : Block := .branch 167 ![10636420114708594398197643235014214017, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 1329552514338574299630590216301019152, 1427247692705959881058285969449495136383139872, 374144419166239053334880641587523935436749248397376] ![(.leaf 0 (Common.fact 313).pointIds 313), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 262).pointIds 262), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 359).pointIds 359), B0113, (.leaf 6 (Common.fact 360).pointIds 360)]
theorem treeEq0112 : B0112.tree = HexagonCover.NBand.M6667_6700.SplitData.node0112 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0113
  · rfl

def B0111 : Block := .branch 168 ![10636420114708594398197643235014214017, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 1329552514338574299630590216301019152, 1427247692705959881058285969449495136383139872, 9527906274737324412155482404830517395520] ![(.leaf 0 (Common.fact 315).pointIds 315), (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 310).pointIds 310), (.leaf 4 (Common.fact 357).pointIds 357), (.leaf 5 (Common.fact 358).pointIds 358), B0112]
theorem treeEq0111 : B0111.tree = HexagonCover.NBand.M6667_6700.SplitData.node0111 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0112

def B0110 : Block := .branch 150 ![10636420114708594398197643235014214017, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 1329552514338574299630590216301019152, 393248, 9527906274737479154660393077364879786048] ![(.leaf 0 (Common.fact 209).pointIds 209), (.leaf 1 (Common.fact 210).pointIds 210), (.leaf 2 (Common.fact 211).pointIds 211), (.leaf 3 (Common.fact 212).pointIds 212), (.leaf 4 (Common.fact 213).pointIds 213), B0111, (.leaf 6 (Common.fact 356).pointIds 356)]
theorem treeEq0110 : B0110.tree = HexagonCover.NBand.M6667_6700.SplitData.node0110 := by
  change Tree.branch (150 : Fin 173) _ = Tree.branch (150 : Fin 173) _
  apply congrArg (Tree.branch (150 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0111
  · rfl

def B0033 : Block := .branch 130 ![10636420114708594398197643235014214017, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 1329552514338574299630590216301019152, 393248, 8166776807053725300806894647637806940224] ![(.leaf 0 (Common.fact 169).pointIds 169), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), B0034, (.leaf 5 (Common.fact 173).pointIds 173), B0110]
theorem treeEq0033 : B0033.tree = HexagonCover.NBand.M6667_6700.SplitData.node0033 := by
  change Tree.branch (130 : Fin 173) _ = Tree.branch (130 : Fin 173) _
  apply congrArg (Tree.branch (130 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0034
  · rfl
  · exact treeEq0110

theorem accepted0033 : B0033.accepted = true := by decide +kernel
theorem checked0033 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0033 (maskNeeds ![10636420114708594398197643235014214017, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 1329552514338574299630590216301019152, 393248, 8166776807053725300806894647637806940224]) := by
  rw [← treeEq0033]
  exact B0033.sound accepted0033
#print axioms checked0033

def Tip0030_0033 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0033 ![10636420114708594398197643235014214017, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 1329552514338574299630590216301019152, 393248, 8166776807053725300806894647637806940224] checked0033
def B0118 : Block := .branch 169 ![2596148429267414967186752771457409, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 1329552514338574299630590216301019152, 393248, 374144419170322441737298077848970316025182115332160] ![(.leaf 0 (Common.fact 370).pointIds 370), (.leaf 1 (Common.fact 363).pointIds 363), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 353).pointIds 353), (.leaf 4 (Common.fact 364).pointIds 364), (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 333).pointIds 333)]
theorem treeEq0118 : B0118.tree = HexagonCover.NBand.M6667_6700.SplitData.node0118 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0117 : Block := .branch 133 ![2596148429267414967186752771457409, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 1329552514338574299630590216301019152, 187072209578355573530071658587684226515959365894176, 374144419159433405995828047018142328587365532565568] ![(.leaf 0 (Common.fact 174).pointIds 174), (.leaf 1 (Common.fact 175).pointIds 175), (.leaf 2 (Common.fact 176).pointIds 176), (.leaf 3 (Common.fact 177).pointIds 177), (.leaf 4 (Common.fact 178).pointIds 178), (.leaf 5 (Common.fact 361).pointIds 361), B0118]
theorem treeEq0117 : B0117.tree = HexagonCover.NBand.M6667_6700.SplitData.node0117 := by
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
  · exact treeEq0118

def B0116 : Block := .branch 167 ![2596148429267414967186752771457409, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 1329552514338574299630590216301019152, 393248, 374144419164888557690529341760539552762756066705472] ![(.leaf 0 (Common.fact 368).pointIds 368), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 262).pointIds 262), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 359).pointIds 359), B0117, (.leaf 6 (Common.fact 369).pointIds 369)]
theorem treeEq0116 : B0116.tree = HexagonCover.NBand.M6667_6700.SplitData.node0116 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0117
  · rfl

def B0115 : Block := .branch 168 ![2596148429267414967186752771457409, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 1329552514338574299630590216301019152, 393248, 8177410630386024585171099730837335703616] ![(.leaf 0 (Common.fact 367).pointIds 367), (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 310).pointIds 310), (.leaf 4 (Common.fact 357).pointIds 357), (.leaf 5 (Common.fact 318).pointIds 318), B0116]
theorem treeEq0115 : B0115.tree = HexagonCover.NBand.M6667_6700.SplitData.node0115 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0116

def B0032 : Block := .branch 123 ![2596148429267414967186752771457409, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 1329552514338574299630590216301019152, 393248, 8166776807053725300806894647637806940224] ![Tip0030_0033, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0115]
theorem treeEq0032 : B0032.tree = HexagonCover.NBand.M6667_6700.SplitData.node0032 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0115

def B0123 : Block := .branch 169 ![2596148429267414967186752771457409, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 1427247692705959881058285969449495136383139872, 374144419170323770965293862764843219832242395676736] ![(.leaf 0 (Common.fact 370).pointIds 370), (.leaf 1 (Common.fact 363).pointIds 363), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 353).pointIds 353), (.leaf 4 (Common.fact 376).pointIds 376), (.leaf 5 (Common.fact 365).pointIds 365), (.leaf 6 (Common.fact 377).pointIds 377)]
theorem treeEq0123 : B0123.tree = HexagonCover.NBand.M6667_6700.SplitData.node0123 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0122 : Block := .branch 133 ![2596148429267414967186752771457409, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 187073636826048279489952716873653676011095748640800, 374144419159434735223823831934015232394425812910144] ![(.leaf 0 (Common.fact 174).pointIds 174), (.leaf 1 (Common.fact 175).pointIds 175), (.leaf 2 (Common.fact 176).pointIds 176), (.leaf 3 (Common.fact 177).pointIds 177), (.leaf 4 (Common.fact 178).pointIds 178), (.leaf 5 (Common.fact 361).pointIds 361), B0123]
theorem treeEq0122 : B0122.tree = HexagonCover.NBand.M6667_6700.SplitData.node0122 := by
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
  · exact treeEq0123

def B0121 : Block := .branch 167 ![2596148429267414967186752771457409, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 1427247692705959881058285969449495136383139872, 374144419164879253095192672649543340814082455896128] ![(.leaf 0 (Common.fact 368).pointIds 368), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 262).pointIds 262), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 374).pointIds 374), B0122, (.leaf 6 (Common.fact 375).pointIds 375)]
theorem treeEq0121 : B0121.tree = HexagonCover.NBand.M6667_6700.SplitData.node0121 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0122
  · rfl

def B0120 : Block := .branch 168 ![2596148429267414967186752771457409, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 1427247692705959881058285969449495136383139872, 8168106035049355474174887782163724894272] ![(.leaf 0 (Common.fact 367).pointIds 367), (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 310).pointIds 310), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 358).pointIds 358), B0121]
theorem treeEq0120 : B0120.tree = HexagonCover.NBand.M6667_6700.SplitData.node0120 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0121

def B0119 : Block := .branch 150 ![2596148429267414967186752771457409, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 393248, 8168106035049510216679798454698087284800] ![(.leaf 0 (Common.fact 209).pointIds 209), (.leaf 1 (Common.fact 210).pointIds 210), (.leaf 2 (Common.fact 211).pointIds 211), (.leaf 3 (Common.fact 212).pointIds 212), (.leaf 4 (Common.fact 213).pointIds 213), B0120, (.leaf 6 (Common.fact 372).pointIds 372)]
theorem treeEq0119 : B0119.tree = HexagonCover.NBand.M6667_6700.SplitData.node0119 := by
  change Tree.branch (150 : Fin 173) _ = Tree.branch (150 : Fin 173) _
  apply congrArg (Tree.branch (150 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0120
  · rfl

def B0031 : Block := .branch 120 ![2596148429267414967186752771457409, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 393248, 8166776807053725300806894647637806940224] ![(.leaf 0 (Common.fact 159).pointIds 159), (.leaf 1 (Common.fact 160).pointIds 160), (.leaf 2 (Common.fact 161).pointIds 161), (.leaf 3 (Common.fact 162).pointIds 162), B0032, (.leaf 5 (Common.fact 163).pointIds 163), B0119]
theorem treeEq0031 : B0031.tree = HexagonCover.NBand.M6667_6700.SplitData.node0031 := by
  change Tree.branch (120 : Fin 173) _ = Tree.branch (120 : Fin 173) _
  apply congrArg (Tree.branch (120 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0032
  · rfl
  · exact treeEq0119

def B0127 : Block := .branch 169 ![2535301201047907534856718909825, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 393248, 374144419170322441737298077848970316025182115332160] ![(.leaf 0 (Common.fact 381).pointIds 381), (.leaf 1 (Common.fact 363).pointIds 363), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 353).pointIds 353), (.leaf 4 (Common.fact 376).pointIds 376), (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 333).pointIds 333)]
theorem treeEq0127 : B0127.tree = HexagonCover.NBand.M6667_6700.SplitData.node0127 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0126 : Block := .branch 133 ![2535301201047907534856718909825, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 187072209578355573530071658587684226515959365894176, 374144419159433405995828047018142328587365532565568] ![(.leaf 0 (Common.fact 174).pointIds 174), (.leaf 1 (Common.fact 175).pointIds 175), (.leaf 2 (Common.fact 176).pointIds 176), (.leaf 3 (Common.fact 177).pointIds 177), (.leaf 4 (Common.fact 178).pointIds 178), (.leaf 5 (Common.fact 361).pointIds 361), B0127]
theorem treeEq0126 : B0126.tree = HexagonCover.NBand.M6667_6700.SplitData.node0126 := by
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
  · exact treeEq0127

def B0125 : Block := .branch 167 ![2535301201047907534856718909825, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 393248, 374144419164877926462711491700970136571521988558912] ![(.leaf 0 (Common.fact 379).pointIds 379), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 262).pointIds 262), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 374).pointIds 374), B0126, (.leaf 6 (Common.fact 380).pointIds 380)]
theorem treeEq0125 : B0125.tree = HexagonCover.NBand.M6667_6700.SplitData.node0125 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0126
  · rfl

def B0124 : Block := .branch 168 ![2535301201047907534856718909825, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 393248, 8166779402568174525601683539603257557056] ![(.leaf 0 (Common.fact 378).pointIds 378), (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 310).pointIds 310), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 318).pointIds 318), B0125]
theorem treeEq0124 : B0124.tree = HexagonCover.NBand.M6667_6700.SplitData.node0124 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0125

def B0030 : Block := .branch 111 ![2535301201047907534856718909825, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 393248, 8166776807053725300806894647637806940224] ![B0031, (.leaf 1 (Common.fact 154).pointIds 154), (.leaf 2 (Common.fact 155).pointIds 155), (.leaf 3 (Common.fact 156).pointIds 156), (.leaf 4 (Common.fact 157).pointIds 157), (.leaf 5 (Common.fact 158).pointIds 158), B0124]
theorem treeEq0030 : B0030.tree = HexagonCover.NBand.M6667_6700.SplitData.node0030 := by
  change Tree.branch (111 : Fin 173) _ = Tree.branch (111 : Fin 173) _
  apply congrArg (Tree.branch (111 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0031
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0124

theorem accepted0030 : B0030.accepted = true := by decide +kernel
theorem checked0030 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0030 (maskNeeds ![2535301201047907534856718909825, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 393248, 8166776807053725300806894647637806940224]) := by
  rw [← treeEq0030]
  exact B0030.sound accepted0030
#print axioms checked0030

def B0168 : Block := .branch 171 ![63805539946105229314349925646227997057, 1096126227998177188652763624537212265841461036546, 1461501637330902918203684910635329987005078575108, 2923003361774091768167693683308920878111708438536, 748288838313424952576278204182482713677958022791184, 92060263772684228656152136994276517341875798048, 1870722095794785053409107864656143448550460486058048] ![(.leaf 0 (Common.fact 490).pointIds 490), (.leaf 1 (Common.fact 491).pointIds 491), (.leaf 2 (Common.fact 492).pointIds 492), (.leaf 3 (Common.fact 493).pointIds 493), (.leaf 4 (Common.fact 494).pointIds 494), (.leaf 5 (Common.fact 495).pointIds 495), (.leaf 6 (Common.fact 496).pointIds 496)]
theorem treeEq0168 : B0168.tree = HexagonCover.NBand.M6667_6700.SplitData.node0168 := by
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

def B0167 : Block := .branch 170 ![63805539946105229314349925646227997057, 1096126227998177188652763624537212265841461036546, 1461501637330902918203684910635329987005078575108, 2923003361774091768167693683308920878111708438536, 748288838313424952576278204182482713677958022791184, 92060263772684228656152136994276517341875798048, 374144419167940465168534595954669636422785562050624] ![(.leaf 0 (Common.fact 484).pointIds 484), (.leaf 1 (Common.fact 485).pointIds 485), (.leaf 2 (Common.fact 486).pointIds 486), (.leaf 3 (Common.fact 487).pointIds 487), (.leaf 4 (Common.fact 488).pointIds 488), (.leaf 5 (Common.fact 489).pointIds 489), B0168]
theorem treeEq0167 : B0167.tree = HexagonCover.NBand.M6667_6700.SplitData.node0167 := by
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
  · exact treeEq0168

def B0170 : Block := .branch 171 ![63805539946105229314349925646227997057, 1096126227998177188652763624537212265841461036546, 77919046967349146032132, 4384504999104994686371301144772748561500459786248, 748288838313424952576278204182482713677958022791184, 92060263772684228656152136994276517341875798048, 1870722095794785053409107864656143448550460486058048] ![(.leaf 0 (Common.fact 490).pointIds 490), (.leaf 1 (Common.fact 491).pointIds 491), (.leaf 2 (Common.fact 499).pointIds 499), (.leaf 3 (Common.fact 500).pointIds 500), (.leaf 4 (Common.fact 494).pointIds 494), (.leaf 5 (Common.fact 495).pointIds 495), (.leaf 6 (Common.fact 496).pointIds 496)]
theorem treeEq0170 : B0170.tree = HexagonCover.NBand.M6667_6700.SplitData.node0170 := by
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

def B0169 : Block := .branch 170 ![63805539946105229314349925646227997057, 1096126227998177188652763624537212265841461036546, 77919046967349146032132, 4384504999104994686371301144772748561500459786248, 748288838313424952576278204182482713677958022791184, 92060263772684228656152136994276517341875798048, 374144419167940465168534595954669636422785562050624] ![(.leaf 0 (Common.fact 484).pointIds 484), (.leaf 1 (Common.fact 485).pointIds 485), (.leaf 2 (Common.fact 497).pointIds 497), (.leaf 3 (Common.fact 498).pointIds 498), (.leaf 4 (Common.fact 488).pointIds 488), (.leaf 5 (Common.fact 489).pointIds 489), B0170]
theorem treeEq0169 : B0169.tree = HexagonCover.NBand.M6667_6700.SplitData.node0169 := by
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
  · exact treeEq0170

def B0171 : Block := .branch 170 ![63805539946105229314349925646227997057, 1096126227998177188652763624537212265841461036546, 77919046967349146032132, 2923003361774091768167693683308920878111708438536, 748288838313424952576278204182482713677958022791184, 92060263772684228656152136994276517341875798048, 1461501648560221026594963612017466410522763591744] ![(.leaf 0 (Common.fact 484).pointIds 484), (.leaf 1 (Common.fact 485).pointIds 485), (.leaf 2 (Common.fact 497).pointIds 497), (.leaf 3 (Common.fact 487).pointIds 487), (.leaf 4 (Common.fact 488).pointIds 488), (.leaf 5 (Common.fact 489).pointIds 489), (.leaf 6 (Common.fact 501).pointIds 501)]
theorem treeEq0171 : B0171.tree = HexagonCover.NBand.M6667_6700.SplitData.node0171 := by
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

def B0166 : Block := .branch 160 ![63805539946105229314349925646227997057, 1096126227998177188652763624537212265841461036546, 77919046967349146032132, 2923003361774091768167693683308920878111708438536, 748288838313424952576278204182482713677958022791184, 92060263772684228656152136994276517341875798048, 374144419167940465168534595954669636422785562050624] ![(.leaf 0 (Common.fact 236).pointIds 236), (.leaf 1 (Common.fact 237).pointIds 237), B0167, B0169, (.leaf 4 (Common.fact 238).pointIds 238), (.leaf 5 (Common.fact 239).pointIds 239), B0171]
theorem treeEq0166 : B0166.tree = HexagonCover.NBand.M6667_6700.SplitData.node0166 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0167
  · exact treeEq0169
  · rfl
  · rfl
  · exact treeEq0171

def B0172 : Block := .branch 170 ![63805539946105229314349925646227997057, 1096126227998177188652763624537212265841461036546, 77919046967349146032132, 87112285931760324017876354838799843352584, 748288838313424952576278204182482713677958022791184, 92060263772684228656152136994276517341875798048, 377067422442602271004941965620102202462097427136576] ![(.leaf 0 (Common.fact 484).pointIds 484), (.leaf 1 (Common.fact 485).pointIds 485), (.leaf 2 (Common.fact 497).pointIds 497), (.leaf 3 (Common.fact 502).pointIds 502), (.leaf 4 (Common.fact 488).pointIds 488), (.leaf 5 (Common.fact 489).pointIds 489), (.leaf 6 (Common.fact 503).pointIds 503)]
theorem treeEq0172 : B0172.tree = HexagonCover.NBand.M6667_6700.SplitData.node0172 := by
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

def B0165 : Block := .branch 161 ![63805539946105229314349925646227997057, 1096126227998177188652763624537212265841461036546, 77919046967349146032132, 87112285931760324017876354838799843352584, 748288838313424952576278204182482713677958022791184, 92060263772684228656152136994276517341875798048, 374144419167940465168534595954669636422785562050624] ![(.leaf 0 (Common.fact 240).pointIds 240), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), B0166, (.leaf 4 (Common.fact 483).pointIds 483), (.leaf 5 (Common.fact 243).pointIds 243), B0172]
theorem treeEq0165 : B0165.tree = HexagonCover.NBand.M6667_6700.SplitData.node0165 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0166
  · rfl
  · rfl
  · exact treeEq0172

def B0174 : Block := .branch 171 ![63805539946105229314349925646227997057, 365375409332725729550921208179070756013494765058, 730750818665451459101842418719324751262788884484, 87112285931760324017876354838799843352584, 748288838313424952576278204182482713677958022791184, 92060263772684228656152136994276517341875798048, 1870722095794785053409107864656143448550460486058048] ![(.leaf 0 (Common.fact 490).pointIds 490), (.leaf 1 (Common.fact 506).pointIds 506), (.leaf 2 (Common.fact 507).pointIds 507), (.leaf 3 (Common.fact 508).pointIds 508), (.leaf 4 (Common.fact 494).pointIds 494), (.leaf 5 (Common.fact 495).pointIds 495), (.leaf 6 (Common.fact 496).pointIds 496)]
theorem treeEq0174 : B0174.tree = HexagonCover.NBand.M6667_6700.SplitData.node0174 := by
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

def B0173 : Block := .branch 170 ![63805539946105229314349925646227997057, 365375409332725729550921208179070756013494765058, 730750818665451459101842418719324751262788884484, 87112285931760324017876354838799843352584, 748288838313424952576278204182482713677958022791184, 92060263772684228656152136994276517341875798048, 374144419167940465168534595954669636422785562050624] ![(.leaf 0 (Common.fact 484).pointIds 484), (.leaf 1 (Common.fact 504).pointIds 504), (.leaf 2 (Common.fact 505).pointIds 505), (.leaf 3 (Common.fact 502).pointIds 502), (.leaf 4 (Common.fact 488).pointIds 488), (.leaf 5 (Common.fact 489).pointIds 489), B0174]
theorem treeEq0173 : B0173.tree = HexagonCover.NBand.M6667_6700.SplitData.node0173 := by
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
  · exact treeEq0174

def B0164 : Block := .branch 159 ![63805539946105229314349925646227997057, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 87112285931760324017876354838799843352584, 748288838313424952576278204182482713677958022791184, 92060263772684228656152136994276517341875798048, 374144419167940465168534595954669636422785562050624] ![(.leaf 0 (Common.fact 232).pointIds 232), B0165, B0173, (.leaf 3 (Common.fact 233).pointIds 233), (.leaf 4 (Common.fact 234).pointIds 234), (.leaf 5 (Common.fact 235).pointIds 235), (.leaf 6 (Common.fact 482).pointIds 482)]
theorem treeEq0164 : B0164.tree = HexagonCover.NBand.M6667_6700.SplitData.node0164 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0165
  · exact treeEq0173
  · rfl
  · rfl
  · rfl
  · rfl

def B0176 : Block := .branch 171 ![63805539946105229314349925646227997057, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 170141183460546602984142639983065325576, 748288838400537238508038450829106613180490684923920, 92060263772684228656152136994276517341875798048, 1870722095794785053409107864656143448550460486058048] ![(.leaf 0 (Common.fact 490).pointIds 490), (.leaf 1 (Common.fact 506).pointIds 506), (.leaf 2 (Common.fact 499).pointIds 499), (.leaf 3 (Common.fact 511).pointIds 511), (.leaf 4 (Common.fact 512).pointIds 512), (.leaf 5 (Common.fact 495).pointIds 495), (.leaf 6 (Common.fact 496).pointIds 496)]
theorem treeEq0176 : B0176.tree = HexagonCover.NBand.M6667_6700.SplitData.node0176 := by
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

def B0175 : Block := .branch 170 ![63805539946105229314349925646227997057, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 170141183460546602984142639983065325576, 748288838400537238508038450829106613180490684923920, 92060263772684228656152136994276517341875798048, 374144419167940465168534595954669636422785562050624] ![(.leaf 0 (Common.fact 484).pointIds 484), (.leaf 1 (Common.fact 504).pointIds 504), (.leaf 2 (Common.fact 497).pointIds 497), (.leaf 3 (Common.fact 509).pointIds 509), (.leaf 4 (Common.fact 510).pointIds 510), (.leaf 5 (Common.fact 489).pointIds 489), B0176]
theorem treeEq0175 : B0175.tree = HexagonCover.NBand.M6667_6700.SplitData.node0175 := by
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
  · exact treeEq0176

def B0163 : Block := .branch 136 ![63805539946105229314349925646227997057, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 170141183460546602984142639983065325576, 748288838313424952576278204182482713677958022791184, 92060263772684228656152136994276517341875798048, 374144419167940465168534595954669636422785562050624] ![(.leaf 0 (Common.fact 190).pointIds 190), (.leaf 1 (Common.fact 191).pointIds 191), (.leaf 2 (Common.fact 192).pointIds 192), B0164, B0175, (.leaf 5 (Common.fact 193).pointIds 193), (.leaf 0 [] 0)]
theorem treeEq0163 : B0163.tree = HexagonCover.NBand.M6667_6700.SplitData.node0163 := by
  change Tree.branch (136 : Fin 173) _ = Tree.branch (136 : Fin 173) _
  apply congrArg (Tree.branch (136 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0164
  · exact treeEq0175
  · rfl
  · rfl

def B0177 : Block := .branch 170 ![63805539946105229314349925646227997057, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 332306999023600220681288032251305992, 748288838313424952576278204182482713677958022791184, 92060263772684228656152136994276517341875798048, 374144419167770323985074126722937949119069677944896] ![(.leaf 0 (Common.fact 484).pointIds 484), (.leaf 1 (Common.fact 504).pointIds 504), (.leaf 2 (Common.fact 497).pointIds 497), (.leaf 3 (Common.fact 513).pointIds 513), (.leaf 4 (Common.fact 488).pointIds 488), (.leaf 5 (Common.fact 489).pointIds 489), (.leaf 6 (Common.fact 514).pointIds 514)]
theorem treeEq0177 : B0177.tree = HexagonCover.NBand.M6667_6700.SplitData.node0177 := by
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

def B0162 : Block := .branch 127 ![63805539946105229314349925646227997057, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 332306999023600220681288032251305992, 748288838313424952576278204182482713677958022791184, 92060263772684228656152136994276517341875798048, 374144419167940465168534595954669636422785562050624] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), B0163, (.leaf 4 (Common.fact 480).pointIds 480), (.leaf 5 (Common.fact 481).pointIds 481), B0177]
theorem treeEq0162 : B0162.tree = HexagonCover.NBand.M6667_6700.SplitData.node0162 := by
  change Tree.branch (127 : Fin 173) _ = Tree.branch (127 : Fin 173) _
  apply congrArg (Tree.branch (127 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0163
  · rfl
  · rfl
  · exact treeEq0177

def B0178 : Block := .branch 170 ![63805539946105229314349925646227997057, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 162417810525494347403032279408648, 748288838313424952576278204182482713677958022791184, 92060263772684228656152136994276517341875798048, 374144419167940797475533542183637862374550632136768] ![(.leaf 0 (Common.fact 484).pointIds 484), (.leaf 1 (Common.fact 504).pointIds 504), (.leaf 2 (Common.fact 497).pointIds 497), (.leaf 3 (Common.fact 515).pointIds 515), (.leaf 4 (Common.fact 488).pointIds 488), (.leaf 5 (Common.fact 489).pointIds 489), (.leaf 6 (Common.fact 516).pointIds 516)]
theorem treeEq0178 : B0178.tree = HexagonCover.NBand.M6667_6700.SplitData.node0178 := by
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

def B0161 : Block := .branch 118 ![63805539946105229314349925646227997057, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 162417810525494347403032279408648, 748288838313424952576278204182482713677958022791184, 92060263772684228656152136994276517341875798048, 374144419167940465168534595954669636422785562050624] ![(.leaf 0 (Common.fact 472).pointIds 472), (.leaf 1 (Common.fact 473).pointIds 473), (.leaf 2 (Common.fact 474).pointIds 474), B0162, (.leaf 4 (Common.fact 475).pointIds 475), (.leaf 5 (Common.fact 476).pointIds 476), B0178]
theorem treeEq0161 : B0161.tree = HexagonCover.NBand.M6667_6700.SplitData.node0161 := by
  change Tree.branch (118 : Fin 173) _ = Tree.branch (118 : Fin 173) _
  apply congrArg (Tree.branch (118 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0162
  · rfl
  · rfl
  · exact treeEq0178

def B0179 : Block := .branch 170 ![63805539946105229314349925646227997057, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 158533696280984011454269120520, 748288838313424952576278204182482713677958022791184, 92060263772684228656152136994276517341875798048, 374144419167940465330793872783882999814363572338752] ![(.leaf 0 (Common.fact 484).pointIds 484), (.leaf 1 (Common.fact 504).pointIds 504), (.leaf 2 (Common.fact 497).pointIds 497), (.leaf 3 (Common.fact 517).pointIds 517), (.leaf 4 (Common.fact 488).pointIds 488), (.leaf 5 (Common.fact 489).pointIds 489), (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq0179 : B0179.tree = HexagonCover.NBand.M6667_6700.SplitData.node0179 := by
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

def B0160 : Block := .branch 107 ![63805539946105229314349925646227997057, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 158533696280984011454269120520, 748288838313424952576278204182482713677958022791184, 92060263772684228656152136994276517341875798048, 374144419167940465168534595954669636422785562050624] ![(.leaf 0 (Common.fact 467).pointIds 467), (.leaf 1 (Common.fact 468).pointIds 468), (.leaf 2 (Common.fact 469).pointIds 469), B0161, (.leaf 4 (Common.fact 470).pointIds 470), (.leaf 5 (Common.fact 471).pointIds 471), B0179]
theorem treeEq0160 : B0160.tree = HexagonCover.NBand.M6667_6700.SplitData.node0160 := by
  change Tree.branch (107 : Fin 173) _ = Tree.branch (107 : Fin 173) _
  apply congrArg (Tree.branch (107 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0161
  · rfl
  · rfl
  · exact treeEq0179

theorem accepted0160 : B0160.accepted = true := by decide +kernel
theorem checked0160 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0160 (maskNeeds ![63805539946105229314349925646227997057, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 158533696280984011454269120520, 748288838313424952576278204182482713677958022791184, 92060263772684228656152136994276517341875798048, 374144419167940465168534595954669636422785562050624]) := by
  rw [← treeEq0160]
  exact B0160.sound accepted0160
#print axioms checked0160

def B0208 : Block := .branch 132 ![385, 1538, 6148, 24584, 748288838314783423587970388204590404493564534947856, 393248, 4863877449038265758882626248155189834582857287729216] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 568).pointIds 568), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 569).pointIds 569)]
theorem treeEq0208 : B0208.tree = HexagonCover.NBand.M6667_6700.SplitData.node0208 := by
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
  · rfl

def B0207 : Block := .branch 170 ![2596148429267414967186752771457409, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 748289195300931171941461146069330565872413954899984, 187163553430688754962459388889728994204687861678112, 3367299772411421170642052979453716022455182363721792] ![(.leaf 0 (Common.fact 561).pointIds 561), (.leaf 1 (Common.fact 562).pointIds 562), (.leaf 2 (Common.fact 497).pointIds 497), (.leaf 3 (Common.fact 519).pointIds 519), (.leaf 4 (Common.fact 563).pointIds 563), (.leaf 5 (Common.fact 564).pointIds 564), B0208]
theorem treeEq0207 : B0207.tree = HexagonCover.NBand.M6667_6700.SplitData.node0207 := by
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
  · exact treeEq0208

def B0206 : Block := .branch 167 ![2598683730467871425989746177868161, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 748289195300931171941461146069330565872413954899984, 91343852333181432387730302044767688728496177184, 3367299772411421172265279573045963771071710818205760] ![(.leaf 0 (Common.fact 384).pointIds 384), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 262).pointIds 262), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 567).pointIds 567), B0207, (.leaf 6 (Common.fact 432).pointIds 432)]
theorem treeEq0206 : B0206.tree = HexagonCover.NBand.M6667_6700.SplitData.node0206 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0207
  · rfl

def B0217 : Block := .branch 172 ![58488627962965565822734697405106618753, 1096126227998177188652763624537212265841461036546, 1461501637330902918203684910635329987005078575108, 2923003361774091768167693683308920878111708438536, 935361047891777867650358292938421132579796827602960, 1496669026065253105047086815218276135416310379446304, 3367299772416185123779579943242317381659975470284864] ![(.leaf 0 (Common.fact 575).pointIds 575), (.leaf 1 (Common.fact 576).pointIds 576), (.leaf 2 (Common.fact 577).pointIds 577), (.leaf 3 (Common.fact 578).pointIds 578), (.leaf 4 (Common.fact 579).pointIds 579), (.leaf 5 (Common.fact 580).pointIds 580), (.leaf 6 (Common.fact 581).pointIds 581)]
theorem treeEq0217 : B0217.tree = HexagonCover.NBand.M6667_6700.SplitData.node0217 := by
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

def B0218 : Block := .branch 172 ![58488627962965565822734697405106618753, 1096126227998177188652763624537212265841461036546, 77919046967349146032132, 4384504999104994686371301144772748561500459786248, 935361047891777867650358292938421132579796827602960, 1496669026065253105047086815218276135416310379446304, 3367299772416185123779579943242317381659975470284864] ![(.leaf 0 (Common.fact 575).pointIds 575), (.leaf 1 (Common.fact 576).pointIds 576), (.leaf 2 (Common.fact 582).pointIds 582), (.leaf 3 (Common.fact 583).pointIds 583), (.leaf 4 (Common.fact 579).pointIds 579), (.leaf 5 (Common.fact 580).pointIds 580), (.leaf 6 (Common.fact 581).pointIds 581)]
theorem treeEq0218 : B0218.tree = HexagonCover.NBand.M6667_6700.SplitData.node0218 := by
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

def B0219 : Block := .branch 172 ![58488627962965565822734697405106618753, 1096126227998177188652763624537212265841461036546, 77919046967349146032132, 2923003361774091768167693683308920878111708438536, 935361047891777867650358292938421132579796827602960, 1496669026065253105047086815218276135416310379446304, 2994616854896804879637640310899665211647712671825984] ![(.leaf 0 (Common.fact 575).pointIds 575), (.leaf 1 (Common.fact 576).pointIds 576), (.leaf 2 (Common.fact 582).pointIds 582), (.leaf 3 (Common.fact 578).pointIds 578), (.leaf 4 (Common.fact 579).pointIds 579), (.leaf 5 (Common.fact 580).pointIds 580), (.leaf 6 (Common.fact 584).pointIds 584)]
theorem treeEq0219 : B0219.tree = HexagonCover.NBand.M6667_6700.SplitData.node0219 := by
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

def B0216 : Block := .branch 160 ![58488627962965565822734697405106618753, 1096126227998177188652763624537212265841461036546, 77919046967349146032132, 2923003361774091768167693683308920878111708438536, 935361047891777867650358292938421132579796827602960, 1496669026065253105047086815218276135416310379446304, 3367299772416185123779579943242317381659975470284864] ![(.leaf 0 (Common.fact 236).pointIds 236), (.leaf 1 (Common.fact 237).pointIds 237), B0217, B0218, (.leaf 4 (Common.fact 238).pointIds 238), (.leaf 5 (Common.fact 239).pointIds 239), B0219]
theorem treeEq0216 : B0216.tree = HexagonCover.NBand.M6667_6700.SplitData.node0216 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0217
  · exact treeEq0218
  · rfl
  · rfl
  · exact treeEq0219

def B0220 : Block := .branch 172 ![58488627962965565822734697405106618753, 1096126227998177188652763624537212265841461036546, 77919046967349146032132, 87112285931760324017876354838799843352584, 935361047891777867650358292938421132579796827602960, 1496669026065253105047086815218276135416310379446304, 3370222775690846929615987312907749947699287335370816] ![(.leaf 0 (Common.fact 575).pointIds 575), (.leaf 1 (Common.fact 576).pointIds 576), (.leaf 2 (Common.fact 582).pointIds 582), (.leaf 3 (Common.fact 585).pointIds 585), (.leaf 4 (Common.fact 579).pointIds 579), (.leaf 5 (Common.fact 580).pointIds 580), (.leaf 6 (Common.fact 586).pointIds 586)]
theorem treeEq0220 : B0220.tree = HexagonCover.NBand.M6667_6700.SplitData.node0220 := by
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

def B0215 : Block := .branch 161 ![58488627962965565822734697405106618753, 1096126227998177188652763624537212265841461036546, 77919046967349146032132, 87112285931760324017876354838799843352584, 935361047891777867650358292938421132579796827602960, 1496669026065253105047086815218276135416310379446304, 3367299772416185123779579943242317381659975470284864] ![(.leaf 0 (Common.fact 240).pointIds 240), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), B0216, (.leaf 4 (Common.fact 574).pointIds 574), (.leaf 5 (Common.fact 243).pointIds 243), B0220]
theorem treeEq0215 : B0215.tree = HexagonCover.NBand.M6667_6700.SplitData.node0215 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0216
  · rfl
  · rfl
  · exact treeEq0220

def B0221 : Block := .branch 172 ![58488627962965565822734697405106618753, 365375409332725729550921208179070756013494765058, 730750818665451459101842418719324751262788884484, 87112285931760324017876354838799843352584, 935361047891777867650358292938421132579796827602960, 1496669026065253105047086815218276135416310379446304, 3367299772416185123779579943242317381659975470284864] ![(.leaf 0 (Common.fact 575).pointIds 575), (.leaf 1 (Common.fact 587).pointIds 587), (.leaf 2 (Common.fact 588).pointIds 588), (.leaf 3 (Common.fact 585).pointIds 585), (.leaf 4 (Common.fact 579).pointIds 579), (.leaf 5 (Common.fact 580).pointIds 580), (.leaf 6 (Common.fact 581).pointIds 581)]
theorem treeEq0221 : B0221.tree = HexagonCover.NBand.M6667_6700.SplitData.node0221 := by
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

def B0214 : Block := .branch 159 ![58488627962965565822734697405106618753, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 87112285931760324017876354838799843352584, 935361047891777867650358292938421132579796827602960, 1496669026065253105047086815218276135416310379446304, 3378991785514832347125209421904047645817222930628672] ![(.leaf 0 (Common.fact 232).pointIds 232), B0215, B0221, (.leaf 3 (Common.fact 233).pointIds 233), (.leaf 4 (Common.fact 234).pointIds 234), (.leaf 5 (Common.fact 235).pointIds 235), (.leaf 6 (Common.fact 573).pointIds 573)]
theorem treeEq0214 : B0214.tree = HexagonCover.NBand.M6667_6700.SplitData.node0214 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0215
  · exact treeEq0221
  · rfl
  · rfl
  · rfl
  · rfl

def B0222 : Block := .branch 172 ![58488627962965565822734697405106618753, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 170141183460546602984142639983065325576, 935361047978890153582118539585045032082329489735696, 1496669026065253105047086815218276135416310379446304, 3367299772416185123779579943242317381659975470284864] ![(.leaf 0 (Common.fact 575).pointIds 575), (.leaf 1 (Common.fact 587).pointIds 587), (.leaf 2 (Common.fact 582).pointIds 582), (.leaf 3 (Common.fact 589).pointIds 589), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 580).pointIds 580), (.leaf 6 (Common.fact 581).pointIds 581)]
theorem treeEq0222 : B0222.tree = HexagonCover.NBand.M6667_6700.SplitData.node0222 := by
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

def B0213 : Block := .branch 136 ![58488627962965565822734697405106618753, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 170141183460546602984142639983065325576, 935361047891777867650358292938421132579796827602960, 1496669026065253105047086815218276135416310379446304, 3378991785514832347125209421904047645817222930628672] ![(.leaf 0 (Common.fact 190).pointIds 190), (.leaf 1 (Common.fact 191).pointIds 191), (.leaf 2 (Common.fact 192).pointIds 192), B0214, B0222, (.leaf 5 (Common.fact 193).pointIds 193), (.leaf 0 [] 0)]
theorem treeEq0213 : B0213.tree = HexagonCover.NBand.M6667_6700.SplitData.node0213 := by
  change Tree.branch (136 : Fin 173) _ = Tree.branch (136 : Fin 173) _
  apply congrArg (Tree.branch (136 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0214
  · exact treeEq0222
  · rfl
  · rfl

def B0223 : Block := .branch 172 ![58488627962965565822734697405106618753, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 170141183460546602984142639983065325576, 935361047891777867650358292938421132579796827602960, 1496669026054364069305616784387448147978493796679712, 3367299772421629641649681133357617260678135410065472] ![(.leaf 0 (Common.fact 575).pointIds 575), (.leaf 1 (Common.fact 587).pointIds 587), (.leaf 2 (Common.fact 582).pointIds 582), (.leaf 3 (Common.fact 589).pointIds 589), (.leaf 4 (Common.fact 579).pointIds 579), (.leaf 5 (Common.fact 591).pointIds 591), (.leaf 6 (Common.fact 592).pointIds 592)]
theorem treeEq0223 : B0223.tree = HexagonCover.NBand.M6667_6700.SplitData.node0223 := by
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

def B0212 : Block := .branch 133 ![58488627962965565822734697405106618753, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 170141183460546602984142639983065325576, 935361047891777867650358292938421132579796827602960, 1496669026054364069305616784387448147978493796679712, 3378991785514832347125209421904047645817222930628672] ![(.leaf 0 (Common.fact 174).pointIds 174), (.leaf 1 (Common.fact 175).pointIds 175), (.leaf 2 (Common.fact 176).pointIds 176), (.leaf 3 (Common.fact 177).pointIds 177), (.leaf 4 (Common.fact 178).pointIds 178), B0213, B0223]
theorem treeEq0212 : B0212.tree = HexagonCover.NBand.M6667_6700.SplitData.node0212 := by
  change Tree.branch (133 : Fin 173) _ = Tree.branch (133 : Fin 173) _
  apply congrArg (Tree.branch (133 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0213
  · exact treeEq0223

def B0211 : Block := .branch 132 ![58488627962965565822734697405106618753, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 170141183460546602984142639983065325576, 935361047891777867650358292938421132579796827602960, 1496669026054364069305616784387448147978493796679712, 3378991785509387829254474406488633652098314639245376] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 572).pointIds 572), (.leaf 5 (Common.fact 142).pointIds 142), B0212]
theorem treeEq0211 : B0211.tree = HexagonCover.NBand.M6667_6700.SplitData.node0211 := by
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
  · exact treeEq0212

def B0210 : Block := .branch 167 ![58488630498266766279193500398513029505, 365375409332725729551540178198713446150944327170, 77919046967349146032132, 170141183460546602984142639983065325576, 748288838313422294120286634350736906063837462102032, 1496669026054364069305616784387448147978493796679712, 3378991785509387830877067174780767286014094742126656] ![(.leaf 0 (Common.fact 384).pointIds 384), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 262).pointIds 262), (.leaf 3 (Common.fact 307).pointIds 307), B0211, (.leaf 5 (Common.fact 571).pointIds 571), (.leaf 6 (Common.fact 432).pointIds 432)]
theorem treeEq0210 : B0210.tree = HexagonCover.NBand.M6667_6700.SplitData.node0210 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0211
  · rfl
  · rfl

def B0209 : Block := .branch 170 ![58488630498266766279193500398513029505, 365375409332725729551540178198713446150944327170, 77919046967349146032132, 170141183460546602984142639983065325576, 748289195299570042473777392215477067442686882054160, 91349427519481065043515685974335850818872672288, 3378991785511429525078592805561547533658685351395392] ![(.leaf 0 (Common.fact 561).pointIds 561), (.leaf 1 (Common.fact 562).pointIds 562), (.leaf 2 (Common.fact 497).pointIds 497), (.leaf 3 (Common.fact 519).pointIds 519), (.leaf 4 (Common.fact 563).pointIds 563), B0210, (.leaf 6 (Common.fact 570).pointIds 570)]
theorem treeEq0209 : B0209.tree = HexagonCover.NBand.M6667_6700.SplitData.node0209 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0210
  · rfl

def B0205 : Block := .branch 130 ![58488630498266766279193500398513029505, 365375409332725729551540178198713446150944327170, 77919046967349146032132, 170141183460546602984142639983065325576, 748289195299570042473777392215477067442686882054160, 91349427519481065043515685974335850818872672288, 3378991785510068395610909051707694035228958278549568] ![(.leaf 0 (Common.fact 169).pointIds 169), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), B0206, (.leaf 5 (Common.fact 173).pointIds 173), B0209]
theorem treeEq0205 : B0205.tree = HexagonCover.NBand.M6667_6700.SplitData.node0205 := by
  change Tree.branch (130 : Fin 173) _ = Tree.branch (130 : Fin 173) _
  apply congrArg (Tree.branch (130 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0206
  · rfl
  · exact treeEq0209

theorem accepted0205 : B0205.accepted = true := by decide +kernel
theorem checked0205 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0205 (maskNeeds ![58488630498266766279193500398513029505, 365375409332725729551540178198713446150944327170, 77919046967349146032132, 170141183460546602984142639983065325576, 748289195299570042473777392215477067442686882054160, 91349427519481065043515685974335850818872672288, 3378991785510068395610909051707694035228958278549568]) := by
  rw [← treeEq0205]
  exact B0205.sound accepted0205
#print axioms checked0205

end HexagonCover.NBand.M6667_6700.SplitTree.Run0001
