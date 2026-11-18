import HexagonCover.NBand.M6900_7100.SplitData
import HexagonCover.NBand.M6900_7100.SplitTree.Run0001
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6900_7100.SplitTree.Run0002
open OwnerTree HexagonCover.NBand.M6900_7100

abbrev Block := Chunk (n := 173) (Certificate := Fin 1199) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def B0259 : Block := .branch 170 ![748288838313422304507415652620848621927823526855041, 302231526962350843233794, 77919046967349146032132, 5846006549663894039735755165580962022322679603208, 11498821742992352557354354734334311401619472, 233840261972987002208454690542538204970878178295840, 374144419179169783276926029476475730485637000200256] ![(.leaf 0 (Common.fact 597).pointIds 597), (.leaf 1 (Common.fact 635).pointIds 635), (.leaf 2 (Common.fact 561).pointIds 561), (.leaf 3 (Common.fact 569).pointIds 569), (.leaf 4 (Common.fact 567).pointIds 567), (.leaf 5 (Common.fact 548).pointIds 548), (.leaf 6 (Common.fact 636).pointIds 636)]
theorem treeEq0259 : B0259.tree = HexagonCover.NBand.M6900_7100.SplitData.node0259 := by
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

def B0258 : Block := .branch 138 ![748288838313422304507415652620848621927823526855041, 302231526962350843233794, 77919046967349146032132, 5846006549663894039814983328095226359916223553544, 11150372599265311570767859136324180753088528, 233840261972987002208454690542538204970878178295840, 374144419179169783277242942126532787836011176001600] ![(.leaf 0 (Common.fact 134).pointIds 134), (.leaf 1 (Common.fact 135).pointIds 135), (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), B0259, (.leaf 5 (Common.fact 138).pointIds 138), (.leaf 6 (Common.fact 634).pointIds 634)]
theorem treeEq0258 : B0258.tree = HexagonCover.NBand.M6900_7100.SplitData.node0258 := by
  change Tree.branch (138 : Fin 173) _ = Tree.branch (138 : Fin 173) _
  apply congrArg (Tree.branch (138 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0259
  · rfl
  · rfl

def B0257 : Block := .branch 139 ![748288838313422304507415652620848621927823526855041, 302231526962350843233794, 77919046967349146032132, 5846006549663894039814983328095226359916223553544, 11150372599265311570767859136324180753088528, 233840261972987002208454690542538204970878178295840, 374144419179169783277242942126532787836011176001600] ![(.leaf 0 (Common.fact 128).pointIds 128), (.leaf 1 (Common.fact 129).pointIds 129), (.leaf 2 (Common.fact 130).pointIds 130), (.leaf 3 (Common.fact 131).pointIds 131), B0258, (.leaf 5 (Common.fact 132).pointIds 132), (.leaf 6 (Common.fact 633).pointIds 633)]
theorem treeEq0257 : B0257.tree = HexagonCover.NBand.M6900_7100.SplitData.node0257 := by
  change Tree.branch (139 : Fin 173) _ = Tree.branch (139 : Fin 173) _
  apply congrArg (Tree.branch (139 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0258
  · rfl
  · rfl

def B0256 : Block := .branch 140 ![748288838313422304507415652620848621927823526855041, 302231526962350843233794, 77919046967349146032132, 5846006549663894039814983328095226359916223553544, 11150372599265311570767859136324180753088528, 233840261972987002208454690542538204970878178295840, 374144419179169783277242942126532787836011176001600] ![(.leaf 0 (Common.fact 122).pointIds 122), (.leaf 1 (Common.fact 123).pointIds 123), (.leaf 2 (Common.fact 124).pointIds 124), (.leaf 3 (Common.fact 125).pointIds 125), B0257, (.leaf 5 (Common.fact 126).pointIds 126), (.leaf 6 (Common.fact 632).pointIds 632)]
theorem treeEq0256 : B0256.tree = HexagonCover.NBand.M6900_7100.SplitData.node0256 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0257
  · rfl
  · rfl

def B0255 : Block := .branch 141 ![748288838313422304507415652620848621927823526855041, 302231526962350843233794, 77919046967349146032132, 5846006549663894039814983328095226359916223553544, 11150372599265311570767859136324180753088528, 233840261972987002208454690542538204970878178295840, 374144419179169783277242942126532787836011176001600] ![(.leaf 0 (Common.fact 116).pointIds 116), (.leaf 1 (Common.fact 117).pointIds 117), (.leaf 2 (Common.fact 118).pointIds 118), (.leaf 3 (Common.fact 119).pointIds 119), B0256, (.leaf 5 (Common.fact 120).pointIds 120), (.leaf 6 (Common.fact 631).pointIds 631)]
theorem treeEq0255 : B0255.tree = HexagonCover.NBand.M6900_7100.SplitData.node0255 := by
  change Tree.branch (141 : Fin 173) _ = Tree.branch (141 : Fin 173) _
  apply congrArg (Tree.branch (141 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0256
  · rfl
  · rfl

def B0254 : Block := .branch 128 ![748288838313422304507415652620848621927823526855041, 302231526962350843233794, 77919046967349146032132, 5846006549323611672894044864631851752484455342088, 16725558898897967356151788704486271129583632, 233840261972987002208454690542538204970878178295840, 374144419179169783277242942126532787836011176001600] ![(.leaf 0 (Common.fact 275).pointIds 275), (.leaf 1 (Common.fact 276).pointIds 276), (.leaf 2 (Common.fact 277).pointIds 277), B0255, (.leaf 4 (Common.fact 629).pointIds 629), (.leaf 5 (Common.fact 279).pointIds 279), (.leaf 6 (Common.fact 630).pointIds 630)]
theorem treeEq0254 : B0254.tree = HexagonCover.NBand.M6900_7100.SplitData.node0254 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0255
  · rfl
  · rfl
  · rfl

def B0253 : Block := .branch 129 ![748288838313422304507415652620848621927823526855041, 302231526962350843233794, 77919046967349146032132, 5846006549323611672894044864631851752484455342088, 16725558898897967356151788704486271129583632, 233840261972987002208454690542538204970878178295840, 374144419178489218543401065199606038621147639578688] ![(.leaf 0 (Common.fact 311).pointIds 311), (.leaf 1 (Common.fact 312).pointIds 312), (.leaf 2 (Common.fact 313).pointIds 313), (.leaf 3 (Common.fact 314).pointIds 314), (.leaf 4 (Common.fact 628).pointIds 628), (.leaf 5 (Common.fact 315).pointIds 315), B0254]
theorem treeEq0253 : B0253.tree = HexagonCover.NBand.M6900_7100.SplitData.node0253 := by
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
  · exact treeEq0254

def B0252 : Block := .branch 130 ![748288838313422304507415652620848621927823526855041, 302231526962350843233794, 77919046967349146032132, 5846006549323611672894044864631851752484455342088, 16725558898897967356151788704486271129583632, 233840261972987002208454690542538204970878178295840, 374144419178489218543401065199606038621147639578688] ![(.leaf 0 (Common.fact 518).pointIds 518), (.leaf 1 (Common.fact 519).pointIds 519), (.leaf 2 (Common.fact 520).pointIds 520), (.leaf 3 (Common.fact 521).pointIds 521), (.leaf 4 (Common.fact 627).pointIds 627), (.leaf 5 (Common.fact 523).pointIds 523), B0253]
theorem treeEq0252 : B0252.tree = HexagonCover.NBand.M6900_7100.SplitData.node0252 := by
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
  · exact treeEq0253

def B0251 : Block := .branch 118 ![748288838313422304507415652620848621927823526855041, 302231526962350843233794, 77919046967349146032132, 5846006549323611672894044864631851752484455342088, 16725558898897967356151788704486271129583632, 233840261972987002208454690542538204970878178295840, 385836432285303218695133066984457293356757536997440] ![(.leaf 0 (Common.fact 281).pointIds 281), (.leaf 1 (Common.fact 282).pointIds 282), (.leaf 2 (Common.fact 283).pointIds 283), B0252, (.leaf 4 (Common.fact 625).pointIds 625), (.leaf 5 (Common.fact 285).pointIds 285), (.leaf 6 (Common.fact 626).pointIds 626)]
theorem treeEq0251 : B0251.tree = HexagonCover.NBand.M6900_7100.SplitData.node0251 := by
  change Tree.branch (118 : Fin 173) _ = Tree.branch (118 : Fin 173) _
  apply congrArg (Tree.branch (118 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0252
  · rfl
  · rfl
  · rfl

def B0250 : Block := .branch 131 ![748288838313422304507415652620848621927823526855041, 302231526962350843233794, 77919046967349146032132, 5846006549323611672894044864631851752484455342088, 16725558898897967356151788704486271129583632, 233840261972987002208454690542538204970878178295840, 385836432282580959759765559276750296497303391305792] ![(.leaf 0 (Common.fact 512).pointIds 512), (.leaf 1 (Common.fact 513).pointIds 513), (.leaf 2 (Common.fact 514).pointIds 514), (.leaf 3 (Common.fact 515).pointIds 515), (.leaf 4 (Common.fact 624).pointIds 624), (.leaf 5 (Common.fact 517).pointIds 517), B0251]
theorem treeEq0250 : B0250.tree = HexagonCover.NBand.M6900_7100.SplitData.node0250 := by
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
  · exact treeEq0251

def B0249 : Block := .branch 101 ![748288838313422304504880351420392163124830120444289, 302231526962350843233794, 77919046967349146032132, 5846006549323611672894044864631851752484455342088, 16725558898897967356151788704486271129583632, 233840261972987002208454690542538204970878178295840, 385836432282580959759765559276750296497303391305792] ![B0250, (.leaf 1 (Common.fact 460).pointIds 460), (.leaf 2 (Common.fact 461).pointIds 461), (.leaf 3 (Common.fact 462).pointIds 462), (.leaf 4 (Common.fact 463).pointIds 463), (.leaf 5 (Common.fact 464).pointIds 464), (.leaf 6 (Common.fact 623).pointIds 623)]
theorem treeEq0249 : B0249.tree = HexagonCover.NBand.M6900_7100.SplitData.node0249 := by
  change Tree.branch (101 : Fin 173) _ = Tree.branch (101 : Fin 173) _
  apply congrArg (Tree.branch (101 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0250
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0248 : Block := .branch 107 ![748288838313422304504880351420392163124830120444289, 302231526962350843233794, 77919046967349146032132, 5846006549323611672894044864631851752484455342088, 16725558898897967356151788704486271129583632, 233840261972987002208454690542538204970878178295840, 385836432282580959759765559276750296497303391305792] ![(.leaf 0 (Common.fact 287).pointIds 287), (.leaf 1 (Common.fact 288).pointIds 288), (.leaf 2 (Common.fact 289).pointIds 289), B0249, (.leaf 4 (Common.fact 621).pointIds 621), (.leaf 5 (Common.fact 291).pointIds 291), (.leaf 6 (Common.fact 622).pointIds 622)]
theorem treeEq0248 : B0248.tree = HexagonCover.NBand.M6900_7100.SplitData.node0248 := by
  change Tree.branch (107 : Fin 173) _ = Tree.branch (107 : Fin 173) _
  apply congrArg (Tree.branch (107 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0249
  · rfl
  · rfl
  · rfl

def B0247 : Block := .branch 162 ![748288838313422304504880351420392163124830120444289, 302231526962350843233794, 77919046967349146032132, 79305533766719673860725170184, 16725558898897967356151788704486271129583632, 233840261972987002208454690542538204970878178295840, 385836432282580959759765559276750296497303391305792] ![(.leaf 0 (Common.fact 350).pointIds 350), (.leaf 1 (Common.fact 351).pointIds 351), (.leaf 2 (Common.fact 352).pointIds 352), B0248, (.leaf 4 (Common.fact 619).pointIds 619), (.leaf 5 (Common.fact 353).pointIds 353), (.leaf 6 (Common.fact 620).pointIds 620)]
theorem treeEq0247 : B0247.tree = HexagonCover.NBand.M6900_7100.SplitData.node0247 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0248
  · rfl
  · rfl
  · rfl

def B0246 : Block := .branch 132 ![748288838313422304504880351420392163124830120444289, 302231526962350843233794, 77919046967349146032132, 79305533766719673860725170184, 16725558898897967356151788704486271129583632, 233840261972987002208454690542538204970878178295840, 385836432277136441889030543861336302778395099922496] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 618).pointIds 618), (.leaf 5 (Common.fact 221).pointIds 221), B0247]
theorem treeEq0246 : B0246.tree = HexagonCover.NBand.M6900_7100.SplitData.node0246 := by
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
  · exact treeEq0247

def B0245 : Block := .branch 133 ![748288838313422304504880351420392163124830120444289, 302231526962350843233794, 77919046967349146032132, 79305533766719673860725170184, 16725558898897967356151788704486271129583632, 233840261972987002208454690542538204970878178295840, 385836432277136441889030543861336302778395099922496] ![(.leaf 0 (Common.fact 210).pointIds 210), (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), (.leaf 4 (Common.fact 617).pointIds 617), (.leaf 5 (Common.fact 215).pointIds 215), B0246]
theorem treeEq0245 : B0245.tree = HexagonCover.NBand.M6900_7100.SplitData.node0245 := by
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
  · exact treeEq0246

def B0244 : Block := .branch 143 ![748288838313422304504880351420392163124830120444289, 302231526962350843233794, 77919046967349146032132, 79305533766719673860725170184, 5575186299632655785383929568162090376593424, 233840261972987002208454690542538204970878178295840, 385836432277136441889030543861336302778395099922496] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), B0245, (.leaf 5 (Common.fact 615).pointIds 615), (.leaf 6 (Common.fact 616).pointIds 616)]
theorem treeEq0244 : B0244.tree = HexagonCover.NBand.M6900_7100.SplitData.node0244 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0245
  · rfl
  · rfl

def B0243 : Block := .branch 125 ![748288838313422304504880351420392163124830120444289, 302231526962350843233794, 77919046967349146032132, 79305533766719673860725170184, 5575186299632655785383929568162090376593424, 233840261972944466912589573234605283144949207269408, 385836432277136441889030853346346124123463824703552] ![(.leaf 0 (Common.fact 614).pointIds 614), (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), B0244, (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq0243 : B0243.tree = HexagonCover.NBand.M6900_7100.SplitData.node0243 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0244
  · rfl

def B0242 : Block := .branch 169 ![10384593717069655257060992658440577, 302232391653479298369026, 77937529740219874547716, 79344219392947341994315767816, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 385836432277136441889030853346346124123463824703552] ![B0243, (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 613).pointIds 613)]
theorem treeEq0242 : B0242.tree = HexagonCover.NBand.M6900_7100.SplitData.node0242 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0243
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0241 : Block := .branch 163 ![10384593717069655257060992658440577, 302232391653479298369026, 77937529740219874547716, 79344219392947341994315767816, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 374144419178489218543401374684615859966216364359744] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), (.leaf 4 (Common.fact 612).pointIds 612), (.leaf 5 (Common.fact 262).pointIds 262), B0242]
theorem treeEq0241 : B0241.tree = HexagonCover.NBand.M6900_7100.SplitData.node0241 := by
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
  · exact treeEq0242

def B0240 : Block := .branch 165 ![10384593717069655257060992658440577, 302232391653479298369026, 77937529740219874547716, 79344219392947341994315767816, 719199032652612596314526914292909658567966736, 187072209578355573530071658587684226515959365894176, 374144419178489218543401374684615859966216364359744] ![(.leaf 0 (Common.fact 355).pointIds 355), (.leaf 1 (Common.fact 356).pointIds 356), (.leaf 2 (Common.fact 357).pointIds 357), (.leaf 3 (Common.fact 358).pointIds 358), (.leaf 4 (Common.fact 611).pointIds 611), B0241, (.leaf 0 [] 0)]
theorem treeEq0240 : B0240.tree = HexagonCover.NBand.M6900_7100.SplitData.node0240 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0241
  · rfl

theorem accepted0240 : B0240.accepted = true := by decide +kernel
theorem checked0240 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node0240 (maskNeeds ![10384593717069655257060992658440577, 302232391653479298369026, 77937529740219874547716, 79344219392947341994315767816, 719199032652612596314526914292909658567966736, 187072209578355573530071658587684226515959365894176, 374144419178489218543401374684615859966216364359744]) := by
  rw [← treeEq0240]
  exact B0240.sound accepted0240
#print axioms checked0240

def Tip0128_0141 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node0141 ![10387129018270111715863986064851329, 618970020579439959454254594, 77937529740219874547716, 79344219392947341994315767816, 713623846352979940529142984724747568191471632, 393248, 374144419178489218867919309373022944059234935373888] HexagonCover.NBand.M6900_7100.SplitTree.Run0001.checked0141
def B0140 : Block := .branch 79 ![748288838313443561768219193004703366976801947517313, 730750818665451459101842416358141510927477900802, 6148, 24584, 98320, 393248, 374144424753675518176056541098525785438169291292736] ![(.leaf 0 (Common.fact 486).pointIds 486), (.leaf 1 (Common.fact 487).pointIds 487), (.leaf 2 (Common.fact 223).pointIds 223), (.leaf 3 (Common.fact 224).pointIds 224), (.leaf 4 (Common.fact 225).pointIds 225), (.leaf 5 (Common.fact 226).pointIds 226), (.leaf 6 (Common.fact 488).pointIds 488)]
theorem treeEq0140 : B0140.tree = HexagonCover.NBand.M6900_7100.SplitData.node0140 := by
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

def B0139 : Block := .branch 159 ![748288838313443561768219193004703366976801947517313, 1099511629314, 6148, 24584, 98320, 393248, 374144424753675518176056541098525785438169291292736] ![(.leaf 0 (Common.fact 484).pointIds 484), B0140, (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 232).pointIds 232), (.leaf 5 (Common.fact 233).pointIds 233), (.leaf 6 (Common.fact 485).pointIds 485)]
theorem treeEq0139 : B0139.tree = HexagonCover.NBand.M6900_7100.SplitData.node0139 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0140
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0138 : Block := .branch 124 ![748288838313422294120286634350736906063837462004097, 1099511629314, 6148, 24584, 98320, 393248, 374144424753675518176056541098525785438169291292736] ![B0139, (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), (.leaf 6 (Common.fact 483).pointIds 483)]
theorem treeEq0138 : B0138.tree = HexagonCover.NBand.M6900_7100.SplitData.node0138 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0139
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0137 : Block := .branch 143 ![748288838313422294120286634350736906063837462004097, 1099511629314, 6148, 24584, 324518553658426726783156020674576, 2854495427947215627233879871820816201736912928, 374144424753675518176056541098525785438169291292736] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 481).pointIds 481), (.leaf 5 (Common.fact 482).pointIds 482), B0138]
theorem treeEq0137 : B0137.tree = HexagonCover.NBand.M6900_7100.SplitData.node0137 := by
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
  · exact treeEq0138

def B0136 : Block := .branch 150 ![748288838313422294120286634350736906063837462004097, 1099511629314, 6148, 24584, 324518553658426726783156020674576, 2854495427947215627233879871820816201736912928, 374144424753675518176056541098525785438169291292736] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), B0137, (.leaf 5 (Common.fact 476).pointIds 476), (.leaf 6 (Common.fact 192).pointIds 192)]
theorem treeEq0136 : B0136.tree = HexagonCover.NBand.M6900_7100.SplitData.node0136 := by
  change Tree.branch (150 : Fin 173) _ = Tree.branch (150 : Fin 173) _
  apply congrArg (Tree.branch (150 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0137
  · rfl
  · rfl

def B0135 : Block := .branch 125 ![841824943102600080887857764845035478124810551165313, 1099511629314, 6148, 24584, 324518553658426726783156020674576, 2854495385411919762116571938898990272765886496, 374144424753675518176056541098525785438169291292736] ![(.leaf 0 (Common.fact 475).pointIds 475), (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), B0136, (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq0135 : B0135.tree = HexagonCover.NBand.M6900_7100.SplitData.node0135 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0136
  · rfl

def B0134 : Block := .branch 169 ![93536104789177786767571130494298572060973089161601, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 713623846353304459082801411451530724212047888, 2854495385411919762116571938898990272765886496, 374144424753675518176056541098525785438169291292736] ![B0135, (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq0134 : B0134.tree = HexagonCover.NBand.M6900_7100.SplitData.node0134 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0135
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0133 : Block := .branch 142 ![93536104789177786767571130494298572060973089161601, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 713623846353304459082801411451530724212047888, 2854495385411919762116571938898990272765886496, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), (.leaf 4 (Common.fact 468).pointIds 468), (.leaf 5 (Common.fact 156).pointIds 156), B0134]
theorem treeEq0133 : B0133.tree = HexagonCover.NBand.M6900_7100.SplitData.node0133 := by
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
  · exact treeEq0134

def B0132 : Block := .branch 166 ![2535301200456458802993406411137, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 713623846353304459082801411451530724212047888, 2854495385411919762116571938898990272765886496, 374144419178489218543400755714596217276078914797632] ![B0133, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq0132 : B0132.tree = HexagonCover.NBand.M6900_7100.SplitData.node0132 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0133
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0131 : Block := .branch 151 ![2535301200456458802993406411137, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 713623846353304459082801411451530724212047888, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 465).pointIds 465), B0132, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq0131 : B0131.tree = HexagonCover.NBand.M6900_7100.SplitData.node0131 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0132
  · rfl

def B0130 : Block := .branch 108 ![10387129018270111715863986064851329, 618970020579439959454254594, 77937529740219874547716, 79344219392947341994315767816, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 318).pointIds 318), (.leaf 1 (Common.fact 319).pointIds 319), (.leaf 2 (Common.fact 320).pointIds 320), (.leaf 3 (Common.fact 321).pointIds 321), B0131, (.leaf 5 (Common.fact 322).pointIds 322), Tip0128_0141]
theorem treeEq0130 : B0130.tree = HexagonCover.NBand.M6900_7100.SplitData.node0130 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0131
  · rfl
  · rfl

def B0234 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 374144419178489218545935747430042854734003596427328] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 604).pointIds 604), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 605).pointIds 605)]
theorem treeEq0234 : B0234.tree = HexagonCover.NBand.M6900_7100.SplitData.node0234 := by
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

def B0233 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 374144419178489218545935747430042854734003596427328] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), B0234, (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 603).pointIds 603)]
theorem treeEq0233 : B0233.tree = HexagonCover.NBand.M6900_7100.SplitData.node0233 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0234
  · rfl
  · rfl

def B0129 : Block := .branch 101 ![10384593717069655257060992658440577, 618970020579439959454254594, 77937529740219874547716, 79344219392947341994315767816, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![B0130, (.leaf 1 (Common.fact 460).pointIds 460), (.leaf 2 (Common.fact 461).pointIds 461), (.leaf 3 (Common.fact 462).pointIds 462), (.leaf 4 (Common.fact 463).pointIds 463), (.leaf 5 (Common.fact 464).pointIds 464), B0233]
theorem treeEq0129 : B0129.tree = HexagonCover.NBand.M6900_7100.SplitData.node0129 := by
  change Tree.branch (101 : Fin 173) _ = Tree.branch (101 : Fin 173) _
  apply congrArg (Tree.branch (101 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0130
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0233

def B0236 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 374144419178489218543402922109664966691559988265024] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 604).pointIds 604), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 607).pointIds 607)]
theorem treeEq0236 : B0236.tree = HexagonCover.NBand.M6900_7100.SplitData.node0236 := by
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

def B0235 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 374144419178489218543402922109664966691559988265024] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), B0236, (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 606).pointIds 606)]
theorem treeEq0235 : B0235.tree = HexagonCover.NBand.M6900_7100.SplitData.node0235 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0236
  · rfl
  · rfl

def B0128 : Block := .branch 91 ![10384593717069655257060992658440577, 618970020579439959454254594, 77937529740219874547716, 79344219392947341994315767816, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![B0129, (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), (.leaf 3 (Common.fact 333).pointIds 333), (.leaf 4 (Common.fact 334).pointIds 334), (.leaf 5 (Common.fact 335).pointIds 335), B0235]
theorem treeEq0128 : B0128.tree = HexagonCover.NBand.M6900_7100.SplitData.node0128 := by
  change Tree.branch (91 : Fin 173) _ = Tree.branch (91 : Fin 173) _
  apply congrArg (Tree.branch (91 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0129
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0235

theorem accepted0128 : B0128.accepted = true := by decide +kernel
theorem checked0128 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node0128 (maskNeeds ![10384593717069655257060992658440577, 618970020579439959454254594, 77937529740219874547716, 79344219392947341994315767816, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq0128]
  exact B0128.sound accepted0128
#print axioms checked0128

def Tip0126_0240 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node0240 ![10384593717069655257060992658440577, 302232391653479298369026, 77937529740219874547716, 79344219392947341994315767816, 719199032652612596314526914292909658567966736, 187072209578355573530071658587684226515959365894176, 374144419178489218543401374684615859966216364359744] checked0240
def Tip0126_0128 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node0128 ![10384593717069655257060992658440577, 618970020579439959454254594, 77937529740219874547716, 79344219392947341994315767816, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] checked0128
def B0239 : Block := .branch 167 ![10384593717069655257060992658440577, 302232391653479298369026, 77937529740219874547716, 79344219392947341994315767816, 719199032652612596314526914292909658567966736, 393248, 374144419178489218543401374684615859966216364359744] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 610).pointIds 610), Tip0126_0240, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq0239 : B0239.tree = HexagonCover.NBand.M6900_7100.SplitData.node0239 := by
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
  · rfl

def B0238 : Block := .branch 142 ![10384593717069655257060992658440577, 302232391653479298369026, 77937529740219874547716, 79344219392947341994315767816, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543401374684615859966216364359744] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), B0239, (.leaf 5 (Common.fact 156).pointIds 156), (.leaf 6 (Common.fact 609).pointIds 609)]
theorem treeEq0238 : B0238.tree = HexagonCover.NBand.M6900_7100.SplitData.node0238 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0239
  · rfl
  · rfl

def B0237 : Block := .branch 144 ![10384593717069655257060992658440577, 302232391653479298369026, 77937529740219874547716, 79344219392947341994315767816, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543401374684615859966216364359744] ![(.leaf 0 (Common.fact 110).pointIds 110), (.leaf 1 (Common.fact 111).pointIds 111), (.leaf 2 (Common.fact 112).pointIds 112), (.leaf 3 (Common.fact 113).pointIds 113), (.leaf 4 (Common.fact 114).pointIds 114), B0238, (.leaf 6 (Common.fact 608).pointIds 608)]
theorem treeEq0237 : B0237.tree = HexagonCover.NBand.M6900_7100.SplitData.node0237 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0238
  · rfl

def B0127 : Block := .branch 89 ![10384593717069655257060992658440577, 302232391653479298369026, 77937529740219874547716, 79344219392947341994315767816, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 104).pointIds 104), Tip0126_0128, (.leaf 2 (Common.fact 106).pointIds 106), (.leaf 3 (Common.fact 107).pointIds 107), (.leaf 4 (Common.fact 108).pointIds 108), (.leaf 5 (Common.fact 109).pointIds 109), B0237]
theorem treeEq0127 : B0127.tree = HexagonCover.NBand.M6900_7100.SplitData.node0127 := by
  change Tree.branch (89 : Fin 173) _ = Tree.branch (89 : Fin 173) _
  apply congrArg (Tree.branch (89 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0237

def B0272 : Block := .branch 79 ![748288838313443561768219193004703366976801947517313, 730750818665451459101842416358141510927477900802, 6148, 24584, 98320, 393248, 385836432277136441888713244355016968746685018144832] ![(.leaf 0 (Common.fact 486).pointIds 486), (.leaf 1 (Common.fact 487).pointIds 487), (.leaf 2 (Common.fact 223).pointIds 223), (.leaf 3 (Common.fact 224).pointIds 224), (.leaf 4 (Common.fact 225).pointIds 225), (.leaf 5 (Common.fact 226).pointIds 226), (.leaf 6 (Common.fact 643).pointIds 643)]
theorem treeEq0272 : B0272.tree = HexagonCover.NBand.M6900_7100.SplitData.node0272 := by
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

def B0271 : Block := .branch 159 ![748288838313443561768219193004703366976801947517313, 1099511629314, 6148, 24584, 98320, 393248, 385836432277136441888713244355016968746685018144832] ![(.leaf 0 (Common.fact 484).pointIds 484), B0272, (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 232).pointIds 232), (.leaf 5 (Common.fact 233).pointIds 233), (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq0271 : B0271.tree = HexagonCover.NBand.M6900_7100.SplitData.node0271 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0272
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0270 : Block := .branch 124 ![748288838313422294120286634350736906063837462004097, 1099511629314, 6148, 24584, 98320, 393248, 385836432277136441888713244355016968746685018144832] ![B0271, (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), (.leaf 6 (Common.fact 641).pointIds 641)]
theorem treeEq0270 : B0270.tree = HexagonCover.NBand.M6900_7100.SplitData.node0270 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0271
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0269 : Block := .branch 132 ![748288838313422294120286634350736906063837462004097, 1099511629314, 6148, 24584, 16725558898897967356151788704486271129583632, 393248, 385836432277136441888713244355016968746685018144832] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 618).pointIds 618), (.leaf 5 (Common.fact 221).pointIds 221), B0270]
theorem treeEq0269 : B0269.tree = HexagonCover.NBand.M6900_7100.SplitData.node0269 := by
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
  · exact treeEq0270

def B0268 : Block := .branch 133 ![748288838313422294120286634350736906063837462004097, 1099511629314, 6148, 24584, 16725558898897967356151788704486271129583632, 393248, 385836432277136441888713244355016968746685018144832] ![(.leaf 0 (Common.fact 210).pointIds 210), (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), (.leaf 4 (Common.fact 617).pointIds 617), (.leaf 5 (Common.fact 215).pointIds 215), B0269]
theorem treeEq0268 : B0268.tree = HexagonCover.NBand.M6900_7100.SplitData.node0268 := by
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
  · exact treeEq0269

def B0267 : Block := .branch 143 ![748288838313422294120286634350736906063837462004097, 1099511629314, 6148, 24584, 5575186299632655785383929568162090376593424, 233840261972987002208454690542538204970878178295840, 385836432277136441888713244355016968746685018144832] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), B0268, (.leaf 5 (Common.fact 615).pointIds 615), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq0267 : B0267.tree = HexagonCover.NBand.M6900_7100.SplitData.node0267 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0268
  · rfl
  · rfl

def B0266 : Block := .branch 125 ![748288838313422304504880351420392163124830120444289, 1099511629314, 6148, 24584, 5575186299632655785383929568162090376593424, 233840261972944466912589573234605283144949207269408, 385836432277136441889030311747578936769593556336704] ![(.leaf 0 (Common.fact 614).pointIds 614), (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), B0267, (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq0266 : B0266.tree = HexagonCover.NBand.M6900_7100.SplitData.node0266 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0267
  · rfl

def B0265 : Block := .branch 169 ![10384593717069655257060992658440577, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 385836432277136441889030311747578936769593556336704] ![B0266, (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 639).pointIds 639)]
theorem treeEq0265 : B0265.tree = HexagonCover.NBand.M6900_7100.SplitData.node0265 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0266
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0264 : Block := .branch 163 ![10384593717069655257060992658440577, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 374144419178489218543400833085848672612346095992896] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), (.leaf 4 (Common.fact 612).pointIds 612), (.leaf 5 (Common.fact 262).pointIds 262), B0265]
theorem treeEq0264 : B0264.tree = HexagonCover.NBand.M6900_7100.SplitData.node0264 := by
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
  · exact treeEq0265

def B0263 : Block := .branch 165 ![10384593717069655257060992658440577, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 187072209578355573530071658587684226515959365894176, 374144419178489218543400833085848672612346095992896] ![(.leaf 0 (Common.fact 355).pointIds 355), (.leaf 1 (Common.fact 356).pointIds 356), (.leaf 2 (Common.fact 357).pointIds 357), (.leaf 3 (Common.fact 358).pointIds 358), (.leaf 4 (Common.fact 611).pointIds 611), B0264, (.leaf 0 [] 0)]
theorem treeEq0263 : B0263.tree = HexagonCover.NBand.M6900_7100.SplitData.node0263 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0264
  · rfl

def B0262 : Block := .branch 167 ![10384593717069655257060992658440577, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 374144419178489218543400833085848672612346095992896] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 610).pointIds 610), B0263, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq0262 : B0262.tree = HexagonCover.NBand.M6900_7100.SplitData.node0262 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0263
  · rfl

def B0261 : Block := .branch 142 ![10384593717069655257060992658440577, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400833085848672612346095992896] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), B0262, (.leaf 5 (Common.fact 156).pointIds 156), (.leaf 6 (Common.fact 638).pointIds 638)]
theorem treeEq0261 : B0261.tree = HexagonCover.NBand.M6900_7100.SplitData.node0261 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0262
  · rfl
  · rfl

def B0260 : Block := .branch 144 ![10384593717069655257060992658440577, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400833085848672612346095992896] ![(.leaf 0 (Common.fact 110).pointIds 110), (.leaf 1 (Common.fact 111).pointIds 111), (.leaf 2 (Common.fact 112).pointIds 112), (.leaf 3 (Common.fact 113).pointIds 113), (.leaf 4 (Common.fact 114).pointIds 114), B0261, (.leaf 6 (Common.fact 637).pointIds 637)]
theorem treeEq0260 : B0260.tree = HexagonCover.NBand.M6900_7100.SplitData.node0260 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0261
  · rfl

def B0126 : Block := .branch 86 ![10384593717069655257060992658440577, 302232391653479298369026, 77937529740219874547716, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 340).pointIds 340), (.leaf 1 (Common.fact 341).pointIds 341), (.leaf 2 (Common.fact 342).pointIds 342), B0127, (.leaf 4 (Common.fact 343).pointIds 343), (.leaf 5 (Common.fact 344).pointIds 344), B0260]
theorem treeEq0126 : B0126.tree = HexagonCover.NBand.M6900_7100.SplitData.node0126 := by
  change Tree.branch (86 : Fin 173) _ = Tree.branch (86 : Fin 173) _
  apply congrArg (Tree.branch (86 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0127
  · rfl
  · rfl
  · exact treeEq0260

theorem accepted0126 : B0126.accepted = true := by decide +kernel
theorem checked0126 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node0126 (maskNeeds ![10384593717069655257060992658440577, 302232391653479298369026, 77937529740219874547716, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq0126]
  exact B0126.sound accepted0126
#print axioms checked0126

def B0301 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 21799339455391174049607026298217750331456] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 672).pointIds 672)]
theorem treeEq0301 : B0301.tree = HexagonCover.NBand.M6900_7100.SplitData.node0301 := by
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

def B0300 : Block := .branch 170 ![10384596192949733827821542456689025, 442793916462578796034, 21287542661060822571012, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21799339455391174049607026298217750331456] ![(.leaf 0 (Common.fact 655).pointIds 655), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 657).pointIds 657), (.leaf 3 (Common.fact 658).pointIds 658), B0301, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 671).pointIds 671)]
theorem treeEq0300 : B0300.tree = HexagonCover.NBand.M6900_7100.SplitData.node0300 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0301
  · rfl
  · rfl

def B0299 : Block := .branch 124 ![10384597430889773113201817355813249, 442793916462578796034, 21287542661060822571012, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21778071807458615395640565385253264818240] ![(.leaf 0 (Common.fact 670).pointIds 670), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B0300]
theorem treeEq0299 : B0299.tree = HexagonCover.NBand.M6900_7100.SplitData.node0299 := by
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
  · exact treeEq0300

def B0309 : Block := .branch 124 ![94266855607843243416434530245027883298303978242433, 1538, 6148, 24584, 98320, 393248, 11172150671072770186163499701709434017808448] ![(.leaf 0 (Common.fact 582).pointIds 582), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), (.leaf 6 (Common.fact 672).pointIds 672)]
theorem treeEq0309 : B0309.tree = HexagonCover.NBand.M6900_7100.SplitData.node0309 := by
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

def B0308 : Block := .branch 159 ![93536104789177791957332687828669741788476011970945, 906694436769665430586882, 6148, 24584, 98320, 393248, 11172150671072770186163499701709434017808448] ![B0309, (.leaf 1 (Common.fact 666).pointIds 666), (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 232).pointIds 232), (.leaf 5 (Common.fact 233).pointIds 233), (.leaf 6 (Common.fact 674).pointIds 674)]
theorem treeEq0308 : B0308.tree = HexagonCover.NBand.M6900_7100.SplitData.node0308 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0309
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0307 : Block := .branch 160 ![93536104789177791957332687828669741788476011970945, 906694436769665430586882, 6148, 24584, 98320, 393248, 11172150671072770186163499701709434017808448] ![(.leaf 0 (Common.fact 299).pointIds 299), (.leaf 1 (Common.fact 664).pointIds 664), B0308, (.leaf 3 (Common.fact 301).pointIds 301), (.leaf 4 (Common.fact 302).pointIds 302), (.leaf 5 (Common.fact 303).pointIds 303), (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq0307 : B0307.tree = HexagonCover.NBand.M6900_7100.SplitData.node0307 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0308
  · rfl
  · rfl
  · rfl
  · rfl

def B0306 : Block := .branch 143 ![93536104789177791957332687828669741788476011970945, 906694436769665430586882, 6148, 24584, 1427247693370573878950743905901398666523017232, 42535295865117307932921825928971419680, 21778071807458615395640565385253264818240] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 577).pointIds 577), (.leaf 5 (Common.fact 498).pointIds 498), B0307]
theorem treeEq0306 : B0306.tree = HexagonCover.NBand.M6900_7100.SplitData.node0306 := by
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
  · exact treeEq0307

def B0305 : Block := .branch 166 ![5192296858534827628530496329220481, 906694436769665430586882, 6148, 24584, 1427247693370573878950743905901398666523017232, 2854495427947215627233879871820816201736912928, 374144419178489218867919309448580807785149258793024] ![B0306, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 576).pointIds 576), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq0305 : B0305.tree = HexagonCover.NBand.M6900_7100.SplitData.node0305 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0306
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0304 : Block := .branch 151 ![5192296858534827628530496329220481, 906694436769665430586882, 6148, 24584, 1427247693370573878950743905901398666523017232, 42535295865117307932921825928971419680, 374144419178489218867919309448580807785149258793024] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 575).pointIds 575), B0305, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq0304 : B0304.tree = HexagonCover.NBand.M6900_7100.SplitData.node0304 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0305
  · rfl

def B0313 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 730750840444187556039796611508432015455350685760] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq0313 : B0313.tree = HexagonCover.NBand.M6900_7100.SplitData.node0313 := by
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

def B0312 : Block := .branch 170 ![10384596192949733827821542456689025, 442793916462578796034, 21287542661060822571012, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 730750840444187556039796611508432015455350685760] ![(.leaf 0 (Common.fact 655).pointIds 655), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 657).pointIds 657), (.leaf 3 (Common.fact 658).pointIds 658), B0313, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 675).pointIds 675)]
theorem treeEq0312 : B0312.tree = HexagonCover.NBand.M6900_7100.SplitData.node0312 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0313
  · rfl
  · rfl

def B0311 : Block := .branch 159 ![748288838313443577345112244489855119139199439077761, 907137158627434459825666, 21287542661060822571012, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21778736096937954195150290505627384414272] ![(.leaf 0 (Common.fact 592).pointIds 592), (.leaf 1 (Common.fact 666).pointIds 666), (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 232).pointIds 232), (.leaf 5 (Common.fact 233).pointIds 233), B0312]
theorem treeEq0311 : B0311.tree = HexagonCover.NBand.M6900_7100.SplitData.node0311 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0312

def B0315 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 21800003744870512849116751418591869927488] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 678).pointIds 678)]
theorem treeEq0315 : B0315.tree = HexagonCover.NBand.M6900_7100.SplitData.node0315 := by
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

def B0314 : Block := .branch 170 ![10384596192949733827821542456689025, 442793916462578796034, 21287542661060822571012, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21800003744870512849116751418591869927488] ![(.leaf 0 (Common.fact 655).pointIds 655), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 657).pointIds 657), (.leaf 3 (Common.fact 658).pointIds 658), B0315, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 677).pointIds 677)]
theorem treeEq0314 : B0314.tree = HexagonCover.NBand.M6900_7100.SplitData.node0314 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0315
  · rfl
  · rfl

def B0310 : Block := .branch 124 ![748288838313422309697179685835888658226234953564545, 907137158627434459825666, 21287542661060822571012, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21778736096937954195150290505627384414272] ![B0311, (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B0314]
theorem treeEq0310 : B0310.tree = HexagonCover.NBand.M6900_7100.SplitData.node0310 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0311
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0314

def B0303 : Block := .branch 119 ![748288838313422309697179685835888658226234953564545, 907137158627434459825666, 21287542661060822571012, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309448580807785149258793024] ![(.leaf 0 (Common.fact 158).pointIds 158), (.leaf 1 (Common.fact 159).pointIds 159), (.leaf 2 (Common.fact 160).pointIds 160), (.leaf 3 (Common.fact 161).pointIds 161), B0304, (.leaf 5 (Common.fact 163).pointIds 163), B0310]
theorem treeEq0303 : B0303.tree = HexagonCover.NBand.M6900_7100.SplitData.node0303 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0304
  · rfl
  · exact treeEq0310

def B0317 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 21778076999755473930468193915749594038336] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 680).pointIds 680)]
theorem treeEq0317 : B0317.tree = HexagonCover.NBand.M6900_7100.SplitData.node0317 := by
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

def B0316 : Block := .branch 170 ![10384596192949733827821542456689025, 442793916462578796034, 21287542661060822571012, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21778076999755473930468193915749594038336] ![(.leaf 0 (Common.fact 655).pointIds 655), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 657).pointIds 657), (.leaf 3 (Common.fact 658).pointIds 658), B0317, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 679).pointIds 679)]
theorem treeEq0316 : B0316.tree = HexagonCover.NBand.M6900_7100.SplitData.node0316 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0317
  · rfl
  · rfl

def B0302 : Block := .branch 112 ![748288838313422304504882827301061029695738624344449, 907137158627434459825666, 21287542661060822571012, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309448580807785149258793024] ![B0303, (.leaf 1 (Common.fact 533).pointIds 533), (.leaf 2 (Common.fact 534).pointIds 534), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 536).pointIds 536), (.leaf 5 (Common.fact 537).pointIds 537), B0316]
theorem treeEq0302 : B0302.tree = HexagonCover.NBand.M6900_7100.SplitData.node0302 := by
  change Tree.branch (112 : Fin 173) _ = Tree.branch (112 : Fin 173) _
  apply congrArg (Tree.branch (112 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0303
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0316

def B0298 : Block := .branch 90 ![748288838313422304504882827301061029695738624344449, 907137158627434459825666, 21287542661060822571012, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309448580807785149258793024] ![B0299, B0302, (.leaf 2 (Common.fact 400).pointIds 400), (.leaf 3 (Common.fact 401).pointIds 401), (.leaf 4 (Common.fact 402).pointIds 402), (.leaf 5 (Common.fact 403).pointIds 403), (.leaf 6 (Common.fact 669).pointIds 669)]
theorem treeEq0298 : B0298.tree = HexagonCover.NBand.M6900_7100.SplitData.node0298 := by
  change Tree.branch (90 : Fin 173) _ = Tree.branch (90 : Fin 173) _
  apply congrArg (Tree.branch (90 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0299
  · exact treeEq0302
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0298 : B0298.accepted = true := by decide +kernel
theorem checked0298 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node0298 (maskNeeds ![748288838313422304504882827301061029695738624344449, 907137158627434459825666, 21287542661060822571012, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309448580807785149258793024]) := by
  rw [← treeEq0298]
  exact B0298.sound accepted0298
#print axioms checked0298

end HexagonCover.NBand.M6900_7100.SplitTree.Run0002
