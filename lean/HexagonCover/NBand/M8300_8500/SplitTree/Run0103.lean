import HexagonCover.NBand.M8300_8500.SplitData
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.SplitTree.Run0103
open OwnerTree HexagonCover.NBand.M8300_8500

abbrev Block := Chunk (n := 177) (Certificate := Fin 1786) (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck

def B7488 : Block := .branch 175 ![51923602410648390402257511457489281, 2993155353253689176481146537402947660284146866980354, 169249614746119002958862340, 8769099026966211631714675139170788711381619204104, 58460065493236116728147393308651320786237301817360, 5708990813359135389350451810719806474502406176, 38536875173141248147194761669062950662288179048480832] ![(.leaf 0 (Common.fact 1610).pointIds 1610), (.leaf 1 (Common.fact 1611).pointIds 1611), (.leaf 2 (Common.fact 1612).pointIds 1612), (.leaf 3 (Common.fact 1613).pointIds 1613), (.leaf 4 (Common.fact 1614).pointIds 1614), (.leaf 5 (Common.fact 1615).pointIds 1615), (.leaf 6 (Common.fact 1616).pointIds 1616)]
theorem treeEq7488 : B7488.tree = HexagonCover.NBand.M8300_8500.SplitData.node7488 := by
  change Tree.branch (175 : Fin 177) _ = Tree.branch (175 : Fin 177) _
  apply congrArg (Tree.branch (175 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7489 : Block := .branch 175 ![51923602410648390402257511457489281, 2993155353253689176481146537402947660284146866980354, 169249614746119002958862340, 8769099026966211631714675139170788711381619204104, 12057388507979949075180399869909334912161443577872, 46773761385402252517907265098731776435464343781408, 38536875173141248147194761669062950662288179048480832] ![(.leaf 0 (Common.fact 1610).pointIds 1610), (.leaf 1 (Common.fact 1611).pointIds 1611), (.leaf 2 (Common.fact 1612).pointIds 1612), (.leaf 3 (Common.fact 1613).pointIds 1613), (.leaf 4 (Common.fact 1617).pointIds 1617), (.leaf 5 (Common.fact 1618).pointIds 1618), (.leaf 6 (Common.fact 1616).pointIds 1616)]
theorem treeEq7489 : B7489.tree = HexagonCover.NBand.M8300_8500.SplitData.node7489 := by
  change Tree.branch (175 : Fin 177) _ = Tree.branch (175 : Fin 177) _
  apply congrArg (Tree.branch (175 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7487 : Block := .branch 165 ![51923602410648390402257511457489281, 2993155353253689176481146537402947660284146866980354, 169249614746119002958862340, 8769099026966211631714675139170788711381619204104, 12057388507979949075180399869909334912161443577872, 5708990813359135389350451810719806474502406176, 38536875173141248147194761669062950662288179048480832] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), B7488, B7489, (.leaf 0 [] 0)]
theorem treeEq7487 : B7487.tree = HexagonCover.NBand.M8300_8500.SplitData.node7487 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7488
  · exact treeEq7489
  · rfl

def B7490 : Block := .branch 175 ![51923602410648390402257511457489281, 2993155353253689176481146537402947660284146866980354, 169249614746119002958862340, 2923092477642599958899935808305656632757889032200, 17903395057303560747995139200774466990785173749776, 5708990813359135389350451810719806474502406176, 38536875173141248147194761669062950662288179048480832] ![(.leaf 0 (Common.fact 1610).pointIds 1610), (.leaf 1 (Common.fact 1611).pointIds 1611), (.leaf 2 (Common.fact 1612).pointIds 1612), (.leaf 3 (Common.fact 1619).pointIds 1619), (.leaf 4 (Common.fact 1620).pointIds 1620), (.leaf 5 (Common.fact 1615).pointIds 1615), (.leaf 6 (Common.fact 1616).pointIds 1616)]
theorem treeEq7490 : B7490.tree = HexagonCover.NBand.M8300_8500.SplitData.node7490 := by
  change Tree.branch (175 : Fin 177) _ = Tree.branch (175 : Fin 177) _
  apply congrArg (Tree.branch (175 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7486 : Block := .branch 162 ![51923602410648390402257511457489281, 2993155353253689176481146537402947660284146866980354, 169249614746119002958862340, 2923092477642599958899935808305656632757889032200, 12057388507979949075180399869909334912161443577872, 5708990813359135389350451810719806474502406176, 38536875173141248147194761669062950662288179048480832] ![(.leaf 0 (Common.fact 355).pointIds 355), (.leaf 1 (Common.fact 356).pointIds 356), (.leaf 2 (Common.fact 357).pointIds 357), B7487, B7490, (.leaf 5 (Common.fact 358).pointIds 358), (.leaf 6 (Common.fact 1609).pointIds 1609)]
theorem treeEq7486 : B7486.tree = HexagonCover.NBand.M8300_8500.SplitData.node7486 := by
  change Tree.branch (162 : Fin 177) _ = Tree.branch (162 : Fin 177) _
  apply congrArg (Tree.branch (162 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7487
  · exact treeEq7490
  · rfl
  · rfl

def B7491 : Block := .branch 175 ![51923602410648390402257511457489281, 2993155353253689176481146537402947660284146866980354, 169249614746119002958862340, 2923092477642599958899935808305656632757889032200, 11694867594032635265391595233669163147520225935376, 365375409375261025416038516111992580842954555424, 38536875173141248147194761669062950662288179048480832] ![(.leaf 0 (Common.fact 1610).pointIds 1610), (.leaf 1 (Common.fact 1611).pointIds 1611), (.leaf 2 (Common.fact 1612).pointIds 1612), (.leaf 3 (Common.fact 1619).pointIds 1619), (.leaf 4 (Common.fact 1621).pointIds 1621), (.leaf 5 (Common.fact 1622).pointIds 1622), (.leaf 6 (Common.fact 1616).pointIds 1616)]
theorem treeEq7491 : B7491.tree = HexagonCover.NBand.M8300_8500.SplitData.node7491 := by
  change Tree.branch (175 : Fin 177) _ = Tree.branch (175 : Fin 177) _
  apply congrArg (Tree.branch (175 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7485 : Block := .branch 158 ![51923602410648390402257511457489281, 2993155353253689176481146537402947660284146866980354, 169249614746119002958862340, 2923092477642599958899935808305656632757889032200, 11694867594032635265391595233669163147520225935376, 5708990813359135389350451810719806474502406176, 38536875173141248147194761669062950662288179048480832] ![(.leaf 0 (Common.fact 306).pointIds 306), (.leaf 1 (Common.fact 307).pointIds 307), (.leaf 2 (Common.fact 308).pointIds 308), (.leaf 3 (Common.fact 309).pointIds 309), B7486, B7491, (.leaf 0 [] 0)]
theorem treeEq7485 : B7485.tree = HexagonCover.NBand.M8300_8500.SplitData.node7485 := by
  change Tree.branch (158 : Fin 177) _ = Tree.branch (158 : Fin 177) _
  apply congrArg (Tree.branch (158 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7486
  · exact treeEq7491
  · rfl

def B7492 : Block := .branch 175 ![51923602410648390402257511457489281, 2993155353253689176481146537402947660284146866980354, 169249614746119002958862340, 2923092477642599958899935808305656632757889032200, 11692018673833522978285264045659832319337836937232, 5708990813359135389350451810719806474502406176, 14591635201607120147265351486411308567235653029855296] ![(.leaf 0 (Common.fact 1610).pointIds 1610), (.leaf 1 (Common.fact 1611).pointIds 1611), (.leaf 2 (Common.fact 1612).pointIds 1612), (.leaf 3 (Common.fact 1619).pointIds 1619), (.leaf 4 (Common.fact 1623).pointIds 1623), (.leaf 5 (Common.fact 1615).pointIds 1615), (.leaf 6 (Common.fact 1624).pointIds 1624)]
theorem treeEq7492 : B7492.tree = HexagonCover.NBand.M8300_8500.SplitData.node7492 := by
  change Tree.branch (175 : Fin 177) _ = Tree.branch (175 : Fin 177) _
  apply congrArg (Tree.branch (175 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7484 : Block := .branch 151 ![51923602410648390402257511457489281, 2993155353253689176481146537402947660284146866980354, 169249614746119002958862340, 2923092477642599958899935808305656632757889032200, 11692018673833522978285264045659832319337836937232, 5708990813359135389350451810719806474502406176, 38536875173141248147194761669062950662288179048480832] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), (.leaf 2 (Common.fact 298).pointIds 298), (.leaf 3 (Common.fact 299).pointIds 299), B7485, (.leaf 5 (Common.fact 300).pointIds 300), B7492]
theorem treeEq7484 : B7484.tree = HexagonCover.NBand.M8300_8500.SplitData.node7484 := by
  change Tree.branch (151 : Fin 177) _ = Tree.branch (151 : Fin 177) _
  apply congrArg (Tree.branch (151 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7485
  · rfl
  · exact treeEq7492

def B7483 : Block := .branch 146 ![51923602410648390402257511457489281, 2993155353253689176481146537402947660284146866980354, 169249614746119002958862340, 2923003274661805836407369665432566039311865110536, 11692018673833522978285264045659832319337836937232, 5708990813359135389350451810719806474502406176, 38536875173141248147194761669062950662288179048480832] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), B7484, (.leaf 4 (Common.fact 1608).pointIds 1608), (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq7483 : B7483.tree = HexagonCover.NBand.M8300_8500.SplitData.node7483 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7484
  · rfl
  · rfl
  · rfl

def B7493 : Block := .branch 175 ![51923602410648390402257511457489281, 2993155353253689176481146537402947660284146866980354, 169249614746119002958862340, 2923003623110949563448356251928164049442513641480, 11692013104091741216364494077144257876155751825424, 5708990813359135389350451810719806474502406176, 14591632352686921034978245155223299236407470640857152] ![(.leaf 0 (Common.fact 1610).pointIds 1610), (.leaf 1 (Common.fact 1611).pointIds 1611), (.leaf 2 (Common.fact 1612).pointIds 1612), (.leaf 3 (Common.fact 1625).pointIds 1625), (.leaf 4 (Common.fact 1626).pointIds 1626), (.leaf 5 (Common.fact 1615).pointIds 1615), (.leaf 6 (Common.fact 1627).pointIds 1627)]
theorem treeEq7493 : B7493.tree = HexagonCover.NBand.M8300_8500.SplitData.node7493 := by
  change Tree.branch (175 : Fin 177) _ = Tree.branch (175 : Fin 177) _
  apply congrArg (Tree.branch (175 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7482 : Block := .branch 142 ![51923602410648390402257511457489281, 2993155353253689176481146537402947660284146866980354, 169249614746119002958862340, 2923003623110949563448356251928164049442513641480, 11692013104091741216364494077144257876155751825424, 5708990813359135389350451810719806474502406176, 38536875173141248147194761669062950662288179048480832] ![(.leaf 0 (Common.fact 282).pointIds 282), (.leaf 1 (Common.fact 283).pointIds 283), (.leaf 2 (Common.fact 284).pointIds 284), (.leaf 3 (Common.fact 285).pointIds 285), B7483, (.leaf 5 (Common.fact 286).pointIds 286), B7493]
theorem treeEq7482 : B7482.tree = HexagonCover.NBand.M8300_8500.SplitData.node7482 := by
  change Tree.branch (142 : Fin 177) _ = Tree.branch (142 : Fin 177) _
  apply congrArg (Tree.branch (142 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7483
  · rfl
  · exact treeEq7493

def B7481 : Block := .branch 87 ![51923602410648390402257511457489281, 2993155353253689176481146537402947660284146866980354, 14507109835446468596471812, 2923003623791514297290233178854913264306050064392, 11692013104091741216364494077144257876155751825424, 5708990813359135389350451810719806474502406176, 38536875173141248147194761669062950662288179048480832] ![(.leaf 0 (Common.fact 343).pointIds 343), (.leaf 1 (Common.fact 344).pointIds 344), B7482, (.leaf 3 (Common.fact 1606).pointIds 1606), (.leaf 4 (Common.fact 345).pointIds 345), (.leaf 5 (Common.fact 346).pointIds 346), (.leaf 6 (Common.fact 1607).pointIds 1607)]
theorem treeEq7481 : B7481.tree = HexagonCover.NBand.M8300_8500.SplitData.node7481 := by
  change Tree.branch (87 : Fin 177) _ = Tree.branch (87 : Fin 177) _
  apply congrArg (Tree.branch (87 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq7482
  · rfl
  · rfl
  · rfl
  · rfl

def B7480 : Block := .branch 138 ![51923602410648390402257511457489281, 2993155353253689176481146537402947660284146866980354, 14507109835446468596471812, 2923003275342370570249246592359315254175401533448, 11692013104091741216364494077144257876155751825424, 5708990813359135389350451810719806474502406176, 38536875173163031535589684870388098252392053335392320] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), B7481, (.leaf 4 (Common.fact 1604).pointIds 1604), (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 1605).pointIds 1605)]
theorem treeEq7480 : B7480.tree = HexagonCover.NBand.M8300_8500.SplitData.node7480 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7481
  · rfl
  · rfl
  · rfl

def B7479 : Block := .branch 132 ![51923602410648390402257511457489281, 2993155353253689176481146537402947660284146866980354, 14507109835446468596471812, 2923003275342370570249246592359315254175401533448, 11692013098647223345629478661730264157247460442128, 5708990813359135389350451810719806474502406176, 38536875173163031535589684870388098252392053335392320] ![(.leaf 0 (Common.fact 267).pointIds 267), (.leaf 1 (Common.fact 268).pointIds 268), (.leaf 2 (Common.fact 269).pointIds 269), (.leaf 3 (Common.fact 270).pointIds 270), B7480, (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 6 (Common.fact 1603).pointIds 1603)]
theorem treeEq7479 : B7479.tree = HexagonCover.NBand.M8300_8500.SplitData.node7479 := by
  change Tree.branch (132 : Fin 177) _ = Tree.branch (132 : Fin 177) _
  apply congrArg (Tree.branch (132 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7480
  · rfl
  · rfl

def B7478 : Block := .branch 152 ![51923602410648390402257511457489281, 2993155353253689176481146537402947660284146866980354, 14507109835446468596471812, 2923003275342370570249246592359315254175401533448, 11692013795545510799711451834721460177508757504016, 42535295865117307932921825928971419680, 38536875173163031535589684870388098252392053335392320] ![(.leaf 0 (Common.fact 301).pointIds 301), (.leaf 1 (Common.fact 302).pointIds 302), (.leaf 2 (Common.fact 303).pointIds 303), (.leaf 3 (Common.fact 304).pointIds 304), (.leaf 4 (Common.fact 1264).pointIds 1264), B7479, (.leaf 6 (Common.fact 1602).pointIds 1602)]
theorem treeEq7478 : B7478.tree = HexagonCover.NBand.M8300_8500.SplitData.node7478 := by
  change Tree.branch (152 : Fin 177) _ = Tree.branch (152 : Fin 177) _
  apply congrArg (Tree.branch (152 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7479
  · rfl

def B7477 : Block := .branch 171 ![51923602410648390402257511457489281, 36028797018965506, 14511841443315773605943300, 2923003275342370570328474754873579591768945483784, 11692013795545510799711451834721460177508757504016, 42535295865117307932921825928971419680, 38536875173163031535589684870388098252392053335392320] ![(.leaf 0 (Common.fact 1008).pointIds 1008), B7478, (.leaf 2 (Common.fact 1535).pointIds 1535), (.leaf 3 (Common.fact 958).pointIds 958), (.leaf 4 (Common.fact 1011).pointIds 1011), (.leaf 5 (Common.fact 563).pointIds 563), (.leaf 6 (Common.fact 1601).pointIds 1601)]
theorem treeEq7477 : B7477.tree = HexagonCover.NBand.M8300_8500.SplitData.node7477 := by
  change Tree.branch (171 : Fin 177) _ = Tree.branch (171 : Fin 177) _
  apply congrArg (Tree.branch (171 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq7478
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7476 : Block := .branch 170 ![51923602410648390402257511457489281, 180143985094821378, 14511841443315773605943300, 2923003275342370570328474754873579591768945483784, 11692013795545510799711451834721460177508757504016, 42535295865117307932921825928971419680, 37040297496536186947349111601686624440264378411384896] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1543).pointIds 1543), (.leaf 2 (Common.fact 1544).pointIds 1544), (.leaf 3 (Common.fact 1600).pointIds 1600), (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), B7477]
theorem treeEq7476 : B7476.tree = HexagonCover.NBand.M8300_8500.SplitData.node7476 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7477

def B7475 : Block := .branch 161 ![51923602410648390402257511457489281, 180143985094821378, 14549620375178730767652868, 680564733921105089441013552457080397832, 11692013795545510799711451834721460177508757504016, 42535295865117307932921825928971419680, 37040297496536186947349111601686624440264378411384896] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1598).pointIds 1598), B7476, (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 1599).pointIds 1599)]
theorem treeEq7475 : B7475.tree = HexagonCover.NBand.M8300_8500.SplitData.node7475 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7476
  · rfl
  · rfl
  · rfl

def B7474 : Block := .branch 129 ![51923602410648390402257511457489281, 180143985094821378, 14549620375178730767652868, 79228162514264337593543974920, 11692013795548169255703021666467267791629318193168, 42535295865117307932921825928971419680, 37040297496536186947349111601686624440264378411384896] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), B7475, (.leaf 4 (Common.fact 1596).pointIds 1596), (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 1597).pointIds 1597)]
theorem treeEq7474 : B7474.tree = HexagonCover.NBand.M8300_8500.SplitData.node7474 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7475
  · rfl
  · rfl
  · rfl

theorem accepted7474 : B7474.accepted = true := by decide +kernel
theorem checked7474 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node7474 (maskNeeds ![51923602410648390402257511457489281, 180143985094821378, 14549620375178730767652868, 79228162514264337593543974920, 11692013795548169255703021666467267791629318193168, 42535295865117307932921825928971419680, 37040297496536186947349111601686624440264378411384896]) := by
  rw [← treeEq7474]
  exact B7474.sound accepted7474
#print axioms checked7474

def Tip7469_7474 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node7474 ![51923602410648390402257511457489281, 180143985094821378, 14549620375178730767652868, 79228162514264337593543974920, 11692013795548169255703021666467267791629318193168, 42535295865117307932921825928971419680, 37040297496536186947349111601686624440264378411384896] checked7474
def B7473 : Block := .branch 163 ![51923602410648390402257511457489281, 180143985094821378, 14549620375178730767652868, 79228162514264337593543974920, 696900945910073543004737003634381857849360, 42535295865117307932921825928971419680, 37040297496536186947349111601686624440264378411384896] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), Tip7469_7474, (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 1595).pointIds 1595)]
theorem treeEq7473 : B7473.tree = HexagonCover.NBand.M8300_8500.SplitData.node7473 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7472 : Block := .branch 169 ![51923602410648390402257511457489281, 180143985094821378, 14549620375178730767652868, 79228162514264337593543974920, 696900945910073543004737003634381857849360, 42535295865117307932921825928971419680, 36292008658222764653228824967335887534200540949381184] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1547).pointIds 1547), (.leaf 2 (Common.fact 1548).pointIds 1548), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 1263).pointIds 1263), (.leaf 5 (Common.fact 540).pointIds 540), B7473]
theorem treeEq7472 : B7472.tree = HexagonCover.NBand.M8300_8500.SplitData.node7472 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7473

def B7497 : Block := .branch 135 ![385, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 24322310248460928900041588103372314934940508106522688] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 589).pointIds 589), (.leaf 6 (Common.fact 1630).pointIds 1630)]
theorem treeEq7497 : B7497.tree = HexagonCover.NBand.M8300_8500.SplitData.node7497 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7496 : Block := .branch 169 ![385, 144115188075857410, 4731607869854765291524, 79228162514264337593543974920, 696898287454081973172991196020261297160208, 393248, 24322310248460928900041588103372314934940508106522688] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1547).pointIds 1547), (.leaf 2 (Common.fact 1548).pointIds 1548), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 1263).pointIds 1263), B7497, (.leaf 6 (Common.fact 1629).pointIds 1629)]
theorem treeEq7496 : B7496.tree = HexagonCover.NBand.M8300_8500.SplitData.node7496 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7497
  · rfl

def B7495 : Block := .branch 161 ![385, 144115188075857410, 4878213818261697370003460, 1496577676626845252854650389321924528368798608154632, 696898287454081973172991196020261297160208, 393248, 24319387245186267094205180733706882368901196241436736] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1598).pointIds 1598), (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B7496]
theorem treeEq7495 : B7495.tree = HexagonCover.NBand.M8300_8500.SplitData.node7495 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7496

def B7494 : Block := .branch 170 ![385, 144115188075857410, 4878213818261697370003460, 664614077120620450716241123684147208, 696898287454081973172991196020261297160208, 393248, 24319387245186267094205180733706882368901196241436736] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1543).pointIds 1543), (.leaf 2 (Common.fact 1544).pointIds 1544), B7495, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 1628).pointIds 1628)]
theorem treeEq7494 : B7494.tree = HexagonCover.NBand.M8300_8500.SplitData.node7494 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7495
  · rfl
  · rfl
  · rfl

def B7471 : Block := .branch 125 ![51923602410648390402257511457489281, 180143985094821378, 14549620375178730767652868, 664614077120620450716241123684147208, 696900945910073543004737003634381857849360, 393248, 36292008658222764653228824967335887534200540949381184] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), B7472, B7494]
theorem treeEq7471 : B7471.tree = HexagonCover.NBand.M8300_8500.SplitData.node7471 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7472
  · exact treeEq7494

def B7502 : Block := .branch 161 ![385, 1538, 4873482210392392360531972, 1496577676626845252854571161159410264031205064204296, 98320, 393248, 36292008658200983923289893335842485751710787223158848] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1598).pointIds 1598), (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 1634).pointIds 1634)]
theorem treeEq7502 : B7502.tree = HexagonCover.NBand.M8300_8500.SplitData.node7502 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7501 : Block := .branch 170 ![385, 144115188075857410, 4878213818261697370003460, 664613997892457936451903530140196872, 98320, 393248, 36292008658244540066255773459165797701462053554225216] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1543).pointIds 1543), (.leaf 2 (Common.fact 1544).pointIds 1544), B7502, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 1633).pointIds 1633)]
theorem treeEq7501 : B7501.tree = HexagonCover.NBand.M8300_8500.SplitData.node7501 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7502
  · rfl
  · rfl
  · rfl

def B7500 : Block := .branch 135 ![385, 144115188075857410, 4878213818261697370003460, 664613997892457936451903530140196872, 98320, 748288838313422294120286634350736906063837462396960, 36292008658200983923289893335842485751710787223158848] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 589).pointIds 589), B7501]
theorem treeEq7500 : B7500.tree = HexagonCover.NBand.M8300_8500.SplitData.node7500 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7501

def B7499 : Block := .branch 169 ![385, 144115188075857410, 4878213818261697370003460, 664614077120620450716241123684147208, 696898287454081973172991196020261297160208, 393248, 36292008658200983923289893335842485751710787223158848] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1547).pointIds 1547), (.leaf 2 (Common.fact 1548).pointIds 1548), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 1263).pointIds 1263), B7500, (.leaf 6 (Common.fact 1632).pointIds 1632)]
theorem treeEq7499 : B7499.tree = HexagonCover.NBand.M8300_8500.SplitData.node7499 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7500
  · rfl

def B7498 : Block := .branch 171 ![385, 144115188075857410, 4878213818261697370003460, 664614077120620450716241123684147208, 696898287454081973172991196020261297160208, 393248, 36292008658200983923289893335842485751710787223158848] ![(.leaf 0 (Common.fact 1008).pointIds 1008), B7499, (.leaf 2 (Common.fact 1535).pointIds 1535), (.leaf 3 (Common.fact 958).pointIds 958), (.leaf 4 (Common.fact 1011).pointIds 1011), (.leaf 5 (Common.fact 563).pointIds 563), (.leaf 6 (Common.fact 1631).pointIds 1631)]
theorem treeEq7498 : B7498.tree = HexagonCover.NBand.M8300_8500.SplitData.node7498 := by
  change Tree.branch (171 : Fin 177) _ = Tree.branch (171 : Fin 177) _
  apply congrArg (Tree.branch (171 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq7499
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7470 : Block := .branch 121 ![51923602410648390402257511457489281, 180143985094821378, 14549620375178730767652868, 664614077120620450716241123684147208, 696898287454081973172991196020261297160208, 393248, 36292008658222764653228824967335887534200540949381184] ![(.leaf 0 (Common.fact 252).pointIds 252), (.leaf 1 (Common.fact 253).pointIds 253), (.leaf 2 (Common.fact 254).pointIds 254), (.leaf 3 (Common.fact 255).pointIds 255), B7471, (.leaf 5 (Common.fact 256).pointIds 256), B7498]
theorem treeEq7470 : B7470.tree = HexagonCover.NBand.M8300_8500.SplitData.node7470 := by
  change Tree.branch (121 : Fin 177) _ = Tree.branch (121 : Fin 177) _
  apply congrArg (Tree.branch (121 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7471
  · rfl
  · exact treeEq7498

def B7508 : Block := .branch 135 ![385, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 36303700671299628488179531244672470208253914122813504] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 574).pointIds 574), (.leaf 6 (Common.fact 1636).pointIds 1636)]
theorem treeEq7508 : B7508.tree = HexagonCover.NBand.M8300_8500.SplitData.node7508 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7507 : Block := .branch 169 ![385, 144115188075857410, 4731607869854765291524, 79228162514264337593543974920, 696898287454081973172991196020261297160208, 233840261972944466912589573234605283144949207269408, 36303700671299628488179531244672470208253914122813504] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1547).pointIds 1547), (.leaf 2 (Common.fact 1548).pointIds 1548), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 1263).pointIds 1263), B7508, (.leaf 6 (Common.fact 1595).pointIds 1595)]
theorem treeEq7507 : B7507.tree = HexagonCover.NBand.M8300_8500.SplitData.node7507 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7508
  · rfl

def B7506 : Block := .branch 171 ![385, 144115188075857410, 4731607869854765291524, 79228162514264337593543974920, 696898287454081973172991196020261297160208, 233840261972944466912589573234605283144949207269408, 36303700671299628488179531244672470208253914122813504] ![(.leaf 0 (Common.fact 1008).pointIds 1008), B7507, (.leaf 2 (Common.fact 1535).pointIds 1535), (.leaf 3 (Common.fact 958).pointIds 958), (.leaf 4 (Common.fact 1011).pointIds 1011), (.leaf 5 (Common.fact 563).pointIds 563), (.leaf 6 (Common.fact 1635).pointIds 1635)]
theorem treeEq7506 : B7506.tree = HexagonCover.NBand.M8300_8500.SplitData.node7506 := by
  change Tree.branch (171 : Fin 177) _ = Tree.branch (171 : Fin 177) _
  apply congrArg (Tree.branch (171 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq7507
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7505 : Block := .branch 163 ![385, 144115188075857410, 4731607869854765291524, 79228162514264337593543974920, 696898952717116972947781101490103478485008, 233840261972944466912589573234605283144949207269408, 36292008658200981264833901766010739944096666662469696] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 601).pointIds 601), (.leaf 5 (Common.fact 329).pointIds 329), B7506]
theorem treeEq7505 : B7505.tree = HexagonCover.NBand.M8300_8500.SplitData.node7505 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7506

def B7504 : Block := .branch 165 ![385, 144115188075857410, 4731607869854765291524, 79228162514264337593543974920, 696898952717116972947781101490103478485008, 187072209578355573530071658587684226515959365894176, 36292008658200981264833901766010739944096666662469696] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 600).pointIds 600), B7505, (.leaf 0 [] 0)]
theorem treeEq7504 : B7504.tree = HexagonCover.NBand.M8300_8500.SplitData.node7504 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7505
  · rfl

def B7503 : Block := .branch 167 ![385, 144115188075857410, 4731607869854765291524, 79228162514264337593543974920, 696898952717116972947781101490103478485008, 393248, 36292008658200981264833901766010739944096666662469696] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 599).pointIds 599), B7504, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq7503 : B7503.tree = HexagonCover.NBand.M8300_8500.SplitData.node7503 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7504
  · rfl

def B7469 : Block := .branch 119 ![51923602410648390402257511457489281, 180143985094821378, 14549620375178730767652868, 79228162514264337593543974920, 696898288103119080489844649586573338312720, 393248, 36292008658222764653228824967335887534200540949381184] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), B7470, B7503, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 1594).pointIds 1594)]
theorem treeEq7469 : B7469.tree = HexagonCover.NBand.M8300_8500.SplitData.node7469 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7470
  · exact treeEq7503
  · rfl
  · rfl

theorem accepted7469 : B7469.accepted = true := by decide +kernel
theorem checked7469 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node7469 (maskNeeds ![51923602410648390402257511457489281, 180143985094821378, 14549620375178730767652868, 79228162514264337593543974920, 696898288103119080489844649586573338312720, 393248, 36292008658222764653228824967335887534200540949381184]) := by
  rw [← treeEq7469]
  exact B7469.sound accepted7469
#print axioms checked7469

def Tip7466_7469 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node7469 ![51923602410648390402257511457489281, 180143985094821378, 14549620375178730767652868, 79228162514264337593543974920, 696898288103119080489844649586573338312720, 393248, 36292008658222764653228824967335887534200540949381184] checked7469
def B7513 : Block := .branch 135 ![385, 1538, 6148, 24584, 98320, 748288838313422335658661502629357934307808096157728, 84182494310260008088532246364457901932182264230707264] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 634).pointIds 634), (.leaf 6 (Common.fact 1644).pointIds 1644)]
theorem treeEq7513 : B7513.tree = HexagonCover.NBand.M8300_8500.SplitData.node7513 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7512 : Block := .branch 169 ![385, 144115188075857410, 4731607869854765291524, 79228162514264337593543974920, 696898287454081973172991196020261297160208, 41538374868278621028243970634154016, 84185417313534669894368653734123334498221576095793216] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1547).pointIds 1547), (.leaf 2 (Common.fact 1548).pointIds 1548), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 1263).pointIds 1263), B7513, (.leaf 6 (Common.fact 1599).pointIds 1599)]
theorem treeEq7512 : B7512.tree = HexagonCover.NBand.M8300_8500.SplitData.node7512 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7513
  · rfl

def B7511 : Block := .branch 161 ![385, 144115188075857410, 4878213818261697370003460, 1496577676626844588240652496863988076465268467982344, 696898287454081973172991196020261297160208, 41538374868278621028243970634154016, 84182494310260008088532246364457901932182264230707264] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1598).pointIds 1598), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B7512]
theorem treeEq7511 : B7511.tree = HexagonCover.NBand.M8300_8500.SplitData.node7511 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7512

def B7510 : Block := .branch 170 ![385, 144115188075857410, 4878213818261697370003460, 79228162514264337593543974920, 696898287454081973172991196020261297160208, 41538374868278621028243970634154016, 84182494310260008088532246364457901932182264230707264] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1543).pointIds 1543), (.leaf 2 (Common.fact 1544).pointIds 1544), B7511, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 1643).pointIds 1643)]
theorem treeEq7510 : B7510.tree = HexagonCover.NBand.M8300_8500.SplitData.node7510 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7511
  · rfl
  · rfl
  · rfl

def B7509 : Block := .branch 175 ![10385227542369769374013540823728513, 1461501637330902918203684832716463163641027364354, 130606499058183131539445764, 324914694470998048471123740352520, 696898288103119080489844649586573338312720, 41538374868278621028243970634154016, 36292008658200981264833901766010739944096666662469696] ![(.leaf 0 (Common.fact 1637).pointIds 1637), (.leaf 1 (Common.fact 1638).pointIds 1638), (.leaf 2 (Common.fact 1639).pointIds 1639), (.leaf 3 (Common.fact 1640).pointIds 1640), (.leaf 4 (Common.fact 1641).pointIds 1641), (.leaf 5 (Common.fact 1642).pointIds 1642), B7510]
theorem treeEq7509 : B7509.tree = HexagonCover.NBand.M8300_8500.SplitData.node7509 := by
  change Tree.branch (175 : Fin 177) _ = Tree.branch (175 : Fin 177) _
  apply congrArg (Tree.branch (175 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7510

def B7468 : Block := .branch 115 ![10385227542369769374013540823728513, 1461501637330902918203684832716463163641027364354, 130606499058183131539445764, 324914694470998048471123740352520, 696898288103119080489844649586573338312720, 393248, 36292008658222764653228824967335887534200540949381184] ![Tip7466_7469, (.leaf 1 (Common.fact 243).pointIds 243), (.leaf 2 (Common.fact 244).pointIds 244), (.leaf 3 (Common.fact 245).pointIds 245), (.leaf 4 (Common.fact 246).pointIds 246), B7509, (.leaf 0 [] 0)]
theorem treeEq7468 : B7468.tree = HexagonCover.NBand.M8300_8500.SplitData.node7468 := by
  change Tree.branch (115 : Fin 177) _ = Tree.branch (115 : Fin 177) _
  apply congrArg (Tree.branch (115 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7509
  · rfl

def B7518 : Block := .branch 135 ![385, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 84182494310260008098916840081527557189243256889147456] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 589).pointIds 589), (.leaf 6 (Common.fact 1649).pointIds 1649)]
theorem treeEq7518 : B7518.tree = HexagonCover.NBand.M8300_8500.SplitData.node7518 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7517 : Block := .branch 169 ![385, 144115188075857410, 4731607869854765291524, 79228162514264337593543974920, 696898287454081973172991196020261297160208, 393248, 84185417313534669904753247451192989755282568754233408] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1547).pointIds 1547), (.leaf 2 (Common.fact 1548).pointIds 1548), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 1263).pointIds 1263), B7518, (.leaf 6 (Common.fact 1648).pointIds 1648)]
theorem treeEq7517 : B7517.tree = HexagonCover.NBand.M8300_8500.SplitData.node7517 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7518
  · rfl

def B7516 : Block := .branch 161 ![385, 144115188075857410, 4878213818261697370003460, 1496577676626844588240652496863988076465268467982344, 696898287454081973172991196020261297160208, 393248, 84182494310260008098916840081527557189243256889147456] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1598).pointIds 1598), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B7517]
theorem treeEq7516 : B7516.tree = HexagonCover.NBand.M8300_8500.SplitData.node7516 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7517

def B7515 : Block := .branch 170 ![385, 144115188075857410, 4878213818261697370003460, 79228162514264337593543974920, 696898287454081973172991196020261297160208, 393248, 84182494310260008098916840081527557189243256889147456] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1543).pointIds 1543), (.leaf 2 (Common.fact 1544).pointIds 1544), B7516, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 1647).pointIds 1647)]
theorem treeEq7515 : B7515.tree = HexagonCover.NBand.M8300_8500.SplitData.node7515 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7516
  · rfl
  · rfl
  · rfl

def B7514 : Block := .branch 175 ![633825300114116952548165288321, 1461501637330902918203684832716463163641027364354, 130606499058183131539445764, 324914694470998048471123740352520, 696898288103119080489844649586573338312720, 393248, 36292008658200981275218495483080395201157659320909888] ![(.leaf 0 (Common.fact 1645).pointIds 1645), (.leaf 1 (Common.fact 1638).pointIds 1638), (.leaf 2 (Common.fact 1639).pointIds 1639), (.leaf 3 (Common.fact 1640).pointIds 1640), (.leaf 4 (Common.fact 1641).pointIds 1641), (.leaf 5 (Common.fact 1646).pointIds 1646), B7515]
theorem treeEq7514 : B7514.tree = HexagonCover.NBand.M8300_8500.SplitData.node7514 := by
  change Tree.branch (175 : Fin 177) _ = Tree.branch (175 : Fin 177) _
  apply congrArg (Tree.branch (175 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7515

def B7467 : Block := .branch 113 ![633825300114116952548165288321, 1461501637330902918203684832716463163641027364354, 130606499058183131539445764, 324914694470998048471123740352520, 696898288103119080489844649586573338312720, 393248, 36292008658222764653228824967335887534200540949381184] ![B7468, (.leaf 1 (Common.fact 238).pointIds 238), (.leaf 2 (Common.fact 239).pointIds 239), (.leaf 3 (Common.fact 240).pointIds 240), (.leaf 4 (Common.fact 241).pointIds 241), (.leaf 5 (Common.fact 242).pointIds 242), B7514]
theorem treeEq7467 : B7467.tree = HexagonCover.NBand.M8300_8500.SplitData.node7467 := by
  change Tree.branch (113 : Fin 177) _ = Tree.branch (113 : Fin 177) _
  apply congrArg (Tree.branch (113 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7468
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7514

def B7521 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 36292008658200981265482938873327593397662978703622208] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 540).pointIds 540), (.leaf 6 (Common.fact 1652).pointIds 1652)]
theorem treeEq7521 : B7521.tree = HexagonCover.NBand.M8300_8500.SplitData.node7521 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7520 : Block := .branch 169 ![2251799813685633, 144115188075857410, 4731607869854765291524, 79228162514264337593543974920, 696898287454081973172991196020261297160208, 393248, 36292008658200981265482938873327593397662978703622208] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1547).pointIds 1547), (.leaf 2 (Common.fact 1548).pointIds 1548), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 1263).pointIds 1263), B7521, (.leaf 6 (Common.fact 1651).pointIds 1651)]
theorem treeEq7520 : B7520.tree = HexagonCover.NBand.M8300_8500.SplitData.node7520 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7521
  · rfl

def B7519 : Block := .branch 171 ![2251799813685633, 144115188075857410, 4731607869854765291524, 79228162514264337593543974920, 696898287454081973172991196020261297160208, 393248, 36292008658200981265482938873327593397662978703622208] ![(.leaf 0 (Common.fact 1008).pointIds 1008), B7520, (.leaf 2 (Common.fact 1535).pointIds 1535), (.leaf 3 (Common.fact 958).pointIds 958), (.leaf 4 (Common.fact 1011).pointIds 1011), (.leaf 5 (Common.fact 563).pointIds 563), (.leaf 6 (Common.fact 1650).pointIds 1650)]
theorem treeEq7519 : B7519.tree = HexagonCover.NBand.M8300_8500.SplitData.node7519 := by
  change Tree.branch (171 : Fin 177) _ = Tree.branch (171 : Fin 177) _
  apply congrArg (Tree.branch (171 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq7520
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7466 : Block := .branch 109 ![633825300114116952548165288321, 1461501637330902918203684832716463163641027364354, 130606499058183131539445764, 324914694470998048471123740352520, 696898287454081973172991196020261297160208, 393248, 36292008658222764653228824967335887534200540949381184] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B7467, (.leaf 5 (Common.fact 211).pointIds 211), B7519]
theorem treeEq7466 : B7466.tree = HexagonCover.NBand.M8300_8500.SplitData.node7466 := by
  change Tree.branch (109 : Fin 177) _ = Tree.branch (109 : Fin 177) _
  apply congrArg (Tree.branch (109 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7467
  · rfl
  · exact treeEq7519

theorem accepted7466 : B7466.accepted = true := by decide +kernel
theorem checked7466 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node7466 (maskNeeds ![633825300114116952548165288321, 1461501637330902918203684832716463163641027364354, 130606499058183131539445764, 324914694470998048471123740352520, 696898287454081973172991196020261297160208, 393248, 36292008658222764653228824967335887534200540949381184]) := by
  rw [← treeEq7466]
  exact B7466.sound accepted7466
#print axioms checked7466

def Tip7463_7466 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node7466 ![633825300114116952548165288321, 1461501637330902918203684832716463163641027364354, 130606499058183131539445764, 324914694470998048471123740352520, 696898287454081973172991196020261297160208, 393248, 36292008658222764653228824967335887534200540949381184] checked7466
def B7525 : Block := .branch 135 ![385, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 36303700671299628488179531244672470208253914122813504] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 589).pointIds 589), (.leaf 6 (Common.fact 1636).pointIds 1636)]
theorem treeEq7525 : B7525.tree = HexagonCover.NBand.M8300_8500.SplitData.node7525 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7524 : Block := .branch 169 ![385, 144115188075857410, 4731607869854765291524, 79228162514264337593543974920, 696898287454081973172991196020261297160208, 393248, 36303700671299628488179531244672470208253914122813504] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1547).pointIds 1547), (.leaf 2 (Common.fact 1548).pointIds 1548), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 1263).pointIds 1263), B7525, (.leaf 6 (Common.fact 1595).pointIds 1595)]
theorem treeEq7524 : B7524.tree = HexagonCover.NBand.M8300_8500.SplitData.node7524 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7525
  · rfl

def B7523 : Block := .branch 171 ![385, 144115188075857410, 4731607869854765291524, 79228162514264337593543974920, 696898287454081973172991196020261297160208, 393248, 36303700671299628488179531244672470208253914122813504] ![(.leaf 0 (Common.fact 1008).pointIds 1008), B7524, (.leaf 2 (Common.fact 1535).pointIds 1535), (.leaf 3 (Common.fact 958).pointIds 958), (.leaf 4 (Common.fact 1011).pointIds 1011), (.leaf 5 (Common.fact 563).pointIds 563), (.leaf 6 (Common.fact 1635).pointIds 1635)]
theorem treeEq7523 : B7523.tree = HexagonCover.NBand.M8300_8500.SplitData.node7523 := by
  change Tree.branch (171 : Fin 177) _ = Tree.branch (171 : Fin 177) _
  apply congrArg (Tree.branch (171 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq7524
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7522 : Block := .branch 163 ![385, 144115188075857410, 4731607869854765291524, 79228162514264337593543974920, 696898287778600526831417922803417317736464, 393248, 36292008658200981264833901766010739944096666662469696] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 1653).pointIds 1653), (.leaf 5 (Common.fact 329).pointIds 329), B7523]
theorem treeEq7522 : B7522.tree = HexagonCover.NBand.M8300_8500.SplitData.node7522 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7523

def B7465 : Block := .branch 108 ![633825300114116952548165288321, 1461501637330902918203684832716463163641027364354, 130606499058183131539445764, 396140812571321687967719776264, 696898287454081973172991196020261297160208, 393248, 36292008658222764653228824967335887534200540949381184] ![(.leaf 0 (Common.fact 452).pointIds 452), (.leaf 1 (Common.fact 453).pointIds 453), (.leaf 2 (Common.fact 454).pointIds 454), Tip7463_7466, B7522, (.leaf 5 (Common.fact 456).pointIds 456), (.leaf 6 (Common.fact 1593).pointIds 1593)]
theorem treeEq7465 : B7465.tree = HexagonCover.NBand.M8300_8500.SplitData.node7465 := by
  change Tree.branch (108 : Fin 177) _ = Tree.branch (108 : Fin 177) _
  apply congrArg (Tree.branch (108 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7522
  · rfl
  · rfl

def B7530 : Block := .branch 135 ![385, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 84182494310260008088532246364457901932182264230707264] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 589).pointIds 589), (.leaf 6 (Common.fact 1644).pointIds 1644)]
theorem treeEq7530 : B7530.tree = HexagonCover.NBand.M8300_8500.SplitData.node7530 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7529 : Block := .branch 169 ![385, 144115188075857410, 4731607869854765291524, 79228162514264337593543974920, 696898287454081973172991196020261297160208, 393248, 84185417313534669894368653734123334498221576095793216] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1547).pointIds 1547), (.leaf 2 (Common.fact 1548).pointIds 1548), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 1263).pointIds 1263), B7530, (.leaf 6 (Common.fact 1599).pointIds 1599)]
theorem treeEq7529 : B7529.tree = HexagonCover.NBand.M8300_8500.SplitData.node7529 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7530
  · rfl

def B7528 : Block := .branch 161 ![385, 144115188075857410, 4878213818261697370003460, 1496577676626844588240652496863988076465268467982344, 696898287454081973172991196020261297160208, 393248, 84182494310260008088532246364457901932182264230707264] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1598).pointIds 1598), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B7529]
theorem treeEq7528 : B7528.tree = HexagonCover.NBand.M8300_8500.SplitData.node7528 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7529

def B7527 : Block := .branch 170 ![385, 144115188075857410, 4878213818261697370003460, 79228162514264337593543974920, 696898287454081973172991196020261297160208, 393248, 84182494310260008088532246364457901932182264230707264] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1543).pointIds 1543), (.leaf 2 (Common.fact 1544).pointIds 1544), B7528, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 1643).pointIds 1643)]
theorem treeEq7527 : B7527.tree = HexagonCover.NBand.M8300_8500.SplitData.node7527 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7528
  · rfl
  · rfl
  · rfl

def B7526 : Block := .branch 175 ![618970019644941937263247745, 1461501637330902918203684832716463163641027364354, 130606499058183131539445764, 396140812571321687967719776264, 696899616682077758088864099827321577504784, 393248, 36292008658200981264833901766010739944096666662469696] ![(.leaf 0 (Common.fact 1654).pointIds 1654), (.leaf 1 (Common.fact 1638).pointIds 1638), (.leaf 2 (Common.fact 1639).pointIds 1639), (.leaf 3 (Common.fact 1655).pointIds 1655), (.leaf 4 (Common.fact 1656).pointIds 1656), (.leaf 5 (Common.fact 1646).pointIds 1646), B7527]
theorem treeEq7526 : B7526.tree = HexagonCover.NBand.M8300_8500.SplitData.node7526 := by
  change Tree.branch (175 : Fin 177) _ = Tree.branch (175 : Fin 177) _
  apply congrArg (Tree.branch (175 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7527

def B7464 : Block := .branch 99 ![618970019644941937263247745, 1461501637330902918203684832716463163641027364354, 130606499058183131539445764, 396140812571321687967719776264, 696899616682077758088864099827321577504784, 393248, 36292008658222764653228824967335887534200540949381184] ![B7465, (.leaf 1 (Common.fact 1592).pointIds 1592), (.leaf 2 (Common.fact 321).pointIds 321), (.leaf 3 (Common.fact 322).pointIds 322), (.leaf 4 (Common.fact 323).pointIds 323), (.leaf 5 (Common.fact 324).pointIds 324), B7526]
theorem treeEq7464 : B7464.tree = HexagonCover.NBand.M8300_8500.SplitData.node7464 := by
  change Tree.branch (99 : Fin 177) _ = Tree.branch (99 : Fin 177) _
  apply congrArg (Tree.branch (99 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7465
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7526

def B7536 : Block := .branch 135 ![385, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 36303700671299628488179531244672470208253914122813504] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 574).pointIds 574), (.leaf 6 (Common.fact 1636).pointIds 1636)]
theorem treeEq7536 : B7536.tree = HexagonCover.NBand.M8300_8500.SplitData.node7536 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7535 : Block := .branch 169 ![385, 144115188075857410, 4731607869854765291524, 79228162514264337593543974920, 696898287454081973172991196020261297160208, 233840261972944466912589573234605283144949207269408, 36303700671299628488179531244672470208253914122813504] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1547).pointIds 1547), (.leaf 2 (Common.fact 1548).pointIds 1548), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 1263).pointIds 1263), B7536, (.leaf 6 (Common.fact 1595).pointIds 1595)]
theorem treeEq7535 : B7535.tree = HexagonCover.NBand.M8300_8500.SplitData.node7535 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7536
  · rfl

def B7534 : Block := .branch 171 ![385, 144115188075857410, 4731607869854765291524, 79228162514264337593543974920, 696898287454081973172991196020261297160208, 233840261972944466912589573234605283144949207269408, 36303700671299628488179531244672470208253914122813504] ![(.leaf 0 (Common.fact 1008).pointIds 1008), B7535, (.leaf 2 (Common.fact 1535).pointIds 1535), (.leaf 3 (Common.fact 958).pointIds 958), (.leaf 4 (Common.fact 1011).pointIds 1011), (.leaf 5 (Common.fact 563).pointIds 563), (.leaf 6 (Common.fact 1635).pointIds 1635)]
theorem treeEq7534 : B7534.tree = HexagonCover.NBand.M8300_8500.SplitData.node7534 := by
  change Tree.branch (171 : Fin 177) _ = Tree.branch (171 : Fin 177) _
  apply congrArg (Tree.branch (171 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq7535
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7533 : Block := .branch 163 ![385, 144115188075857410, 4731607869854765291524, 79228162514264337593543974920, 696898287454398885823048253370635472961552, 233840261972944466912589573234605283144949207269408, 36292008658200981264833901766010739944096666662469696] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 1659).pointIds 1659), (.leaf 5 (Common.fact 329).pointIds 329), B7534]
theorem treeEq7533 : B7533.tree = HexagonCover.NBand.M8300_8500.SplitData.node7533 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7534

def B7532 : Block := .branch 165 ![385, 144115188075857410, 4731607869854765291524, 79228162514264337593543974920, 696898287454398885823048253370635472961552, 187072209578355573530071658587684226515959365894176, 36292008658200981264833901766010739944096666662469696] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 1658).pointIds 1658), B7533, (.leaf 0 [] 0)]
theorem treeEq7532 : B7532.tree = HexagonCover.NBand.M8300_8500.SplitData.node7532 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7533
  · rfl

def B7531 : Block := .branch 167 ![385, 144115188075857410, 4731607869854765291524, 79228162514264337593543974920, 696898287454398885823048253370635472961552, 393248, 36292008658200981264833901766010739944096666662469696] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 1657).pointIds 1657), B7532, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq7531 : B7531.tree = HexagonCover.NBand.M8300_8500.SplitData.node7531 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7532
  · rfl

def B7463 : Block := .branch 98 ![618970019644941937263247745, 1461501637330902918203684832716463163641027364354, 130606499058183131539445764, 79228162514264337593543974920, 696899616682077758088864099827321577504784, 393248, 36292008658222764653228824967335887534200540949381184] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), B7464, B7531, (.leaf 5 (Common.fact 334).pointIds 334), (.leaf 6 (Common.fact 1591).pointIds 1591)]
theorem treeEq7463 : B7463.tree = HexagonCover.NBand.M8300_8500.SplitData.node7463 := by
  change Tree.branch (98 : Fin 177) _ = Tree.branch (98 : Fin 177) _
  apply congrArg (Tree.branch (98 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7464
  · exact treeEq7531
  · rfl
  · rfl

theorem accepted7463 : B7463.accepted = true := by decide +kernel
theorem checked7463 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node7463 (maskNeeds ![618970019644941937263247745, 1461501637330902918203684832716463163641027364354, 130606499058183131539445764, 79228162514264337593543974920, 696899616682077758088864099827321577504784, 393248, 36292008658222764653228824967335887534200540949381184]) := by
  rw [← treeEq7463]
  exact B7463.sound accepted7463
#print axioms checked7463

end HexagonCover.NBand.M8300_8500.SplitTree.Run0103
