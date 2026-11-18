import HexagonCover.NBand.M6667_6700.SplitData
import HexagonCover.NBand.M6667_6700.SplitTree.Run0001
import HexagonCover.NBand.M6667_6700.SplitTree.Run0003
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6667_6700.SplitTree.Run0004
open OwnerTree HexagonCover.NBand.M6667_6700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1334) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip0133_0299 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0299 ![2598683730467871425989746177868161, 618970609938501595666843138, 77919046967349146032132, 96714065569170333976518664, 98320, 21778071482940061661655974875633165926432, 6360455125664090165935142324373021175280070756401216] HexagonCover.NBand.M6667_6700.SplitTree.Run0003.checked0299
def Tip0133_0138 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0138 ![2535301201047907534856718909825, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 356986147748353490757864740161378849420050448, 21778071482940061661655974875633165926432, 374144419156711148683370374995130933666600027947072] HexagonCover.NBand.M6667_6700.SplitTree.Run0003.checked0138
def B0298 : Block := .branch 132 ![385, 1538, 6148, 24584, 664613997892457936451903530140270608, 393248, 7108743963977511794467875405290541449090910016503872] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 421).pointIds 421), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 664).pointIds 664)]
theorem treeEq0298 : B0298.tree = HexagonCover.NBand.M6667_6700.SplitData.node0298 := by
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

def B0297 : Block := .branch 169 ![2535301200457611724498013258113, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 664613997892457936451903530140270608, 393248, 6360455125664089500347588770939804543027072554500160] ![(.leaf 0 (Common.fact 387).pointIds 387), (.leaf 1 (Common.fact 363).pointIds 363), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 353).pointIds 353), (.leaf 4 (Common.fact 420).pointIds 420), (.leaf 5 (Common.fact 371).pointIds 371), B0298]
theorem treeEq0297 : B0297.tree = HexagonCover.NBand.M6667_6700.SplitData.node0297 := by
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
  · exact treeEq0298

def B0296 : Block := .branch 119 ![2598683730467871425989746177868161, 618970609938501595666843138, 77919046967349146032132, 96714065569170333976518664, 98320, 21778071482940061661655974875633165926432, 6360455125664089501645662985573511450159696636805184] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), B0297, (.leaf 5 (Common.fact 419).pointIds 419), Tip0133_0299]
theorem treeEq0296 : B0296.tree = HexagonCover.NBand.M6667_6700.SplitData.node0296 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0297
  · rfl
  · rfl

def B0322 : Block := .branch 132 ![385, 1538, 6148, 24584, 664613997892457936451903530140270608, 393248, 7108743963977511797063390009257841148655409829511232] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 421).pointIds 421), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 654).pointIds 654)]
theorem treeEq0322 : B0322.tree = HexagonCover.NBand.M6667_6700.SplitData.node0322 := by
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

def B0321 : Block := .branch 169 ![2535301200457611724498013258113, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 664613997892457936451903530140270608, 393248, 6360455125664089502943103374907104242591572367507520] ![(.leaf 0 (Common.fact 387).pointIds 387), (.leaf 1 (Common.fact 363).pointIds 363), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 353).pointIds 353), (.leaf 4 (Common.fact 420).pointIds 420), (.leaf 5 (Common.fact 371).pointIds 371), B0322]
theorem treeEq0321 : B0321.tree = HexagonCover.NBand.M6667_6700.SplitData.node0321 := by
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
  · exact treeEq0322

def B0325 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917778679099731358651625140063766194946112] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 657).pointIds 657)]
theorem treeEq0325 : B0325.tree = HexagonCover.NBand.M6667_6700.SplitData.node0325 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0324 : Block := .branch 171 ![2535301200457611724498013258113, 618970609938501595666843138, 77919046967349146032132, 96714065569170333976518664, 748288838313422294120286634350736906063837462102032, 21778071482940061661655974875633165926432, 6360455125664089502618584821248677515808416346931264] ![(.leaf 0 (Common.fact 666).pointIds 666), (.leaf 1 (Common.fact 667).pointIds 667), (.leaf 2 (Common.fact 499).pointIds 499), (.leaf 3 (Common.fact 539).pointIds 539), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 541).pointIds 541), B0325]
theorem treeEq0324 : B0324.tree = HexagonCover.NBand.M6667_6700.SplitData.node0324 := by
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
  · exact treeEq0325

def B0323 : Block := .branch 169 ![2535301200457611724498013258113, 618970609938501595666843138, 77919046967349146032132, 96714065569170333976518664, 98320, 21778071482940061661655974875633165926432, 6360455125664090167232582713706613967711946487103552] ![(.leaf 0 (Common.fact 387).pointIds 387), (.leaf 1 (Common.fact 363).pointIds 363), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 353).pointIds 353), B0324, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 655).pointIds 655)]
theorem treeEq0323 : B0323.tree = HexagonCover.NBand.M6667_6700.SplitData.node0323 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0324
  · rfl
  · rfl

def B0320 : Block := .branch 119 ![2535301200457611724498013258113, 618970609938501595666843138, 77919046967349146032132, 96714065569170333976518664, 98320, 21778071482940061661655974875633165926432, 6360455125664089502943103374907104242591572367507520] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), B0321, (.leaf 5 (Common.fact 419).pointIds 419), B0323]
theorem treeEq0320 : B0320.tree = HexagonCover.NBand.M6667_6700.SplitData.node0320 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0321
  · rfl
  · exact treeEq0323

def B0327 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 6360455125664089505539251804174518056856820532117568] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 659).pointIds 659), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 660).pointIds 660)]
theorem treeEq0327 : B0327.tree = HexagonCover.NBand.M6667_6700.SplitData.node0327 := by
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
  · rfl

def B0326 : Block := .branch 171 ![2535301200457611724498013258113, 618970609938501595666843138, 77919046967349146032132, 77371252455336267181219848, 356811923176489970264571492362373784095784976, 21778071482940061661655974875633165926432, 6360455125664089505539251804174518056856820532117568] ![(.leaf 0 (Common.fact 666).pointIds 666), (.leaf 1 (Common.fact 667).pointIds 667), (.leaf 2 (Common.fact 499).pointIds 499), (.leaf 3 (Common.fact 539).pointIds 539), B0327, (.leaf 5 (Common.fact 541).pointIds 541), (.leaf 6 (Common.fact 658).pointIds 658)]
theorem treeEq0326 : B0326.tree = HexagonCover.NBand.M6667_6700.SplitData.node0326 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0327
  · rfl
  · rfl

def B0319 : Block := .branch 112 ![2535301200457611724498013258113, 618970609938501595666843138, 77919046967349146032132, 96714065569170333976518664, 356811923176489970264571492362373784095784976, 21778071482940061661655974875633165926432, 6360455125664089502943103374907104242591572367507520] ![B0320, (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 650).pointIds 650), (.leaf 3 (Common.fact 651).pointIds 651), (.leaf 4 (Common.fact 652).pointIds 652), (.leaf 5 (Common.fact 653).pointIds 653), B0326]
theorem treeEq0319 : B0319.tree = HexagonCover.NBand.M6667_6700.SplitData.node0319 := by
  change Tree.branch (112 : Fin 173) _ = Tree.branch (112 : Fin 173) _
  apply congrArg (Tree.branch (112 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0320
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0326

def B0295 : Block := .branch 111 ![2535301200457611724498013258113, 618970609938501595666843138, 77919046967349146032132, 96714065569170333976518664, 356811923176489970264571492362373784095784976, 21778071482940061661655974875633165926432, 6360455125664089501645662985573511450159696636805184] ![B0296, (.leaf 1 (Common.fact 154).pointIds 154), (.leaf 2 (Common.fact 155).pointIds 155), (.leaf 3 (Common.fact 156).pointIds 156), (.leaf 4 (Common.fact 157).pointIds 157), (.leaf 5 (Common.fact 158).pointIds 158), B0319]
theorem treeEq0295 : B0295.tree = HexagonCover.NBand.M6667_6700.SplitData.node0295 := by
  change Tree.branch (111 : Fin 173) _ = Tree.branch (111 : Fin 173) _
  apply congrArg (Tree.branch (111 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0296
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0319

def B0294 : Block := .branch 138 ![2535301200457611724498013258113, 618970609938501595666843138, 77919046967349146032132, 96714065569170333976518664, 356811923176489970264571492362373784095784976, 21778071482940061661655974875633165926432, 6360455125664089501645662985573511450159696636805184] ![(.leaf 0 (Common.fact 643).pointIds 643), (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 645).pointIds 645), (.leaf 3 (Common.fact 646).pointIds 646), B0295, (.leaf 5 (Common.fact 647).pointIds 647), (.leaf 6 (Common.fact 663).pointIds 663)]
theorem treeEq0294 : B0294.tree = HexagonCover.NBand.M6667_6700.SplitData.node0294 := by
  change Tree.branch (138 : Fin 173) _ = Tree.branch (138 : Fin 173) _
  apply congrArg (Tree.branch (138 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0295
  · rfl
  · rfl

def B0293 : Block := .branch 172 ![2535301200457611724498013258113, 618970609938501595666843138, 77919046967349146032132, 96714065569170333976518664, 356986147748353490757864740161378849420050448, 21778071482940061661655974875633165926432, 374144419156711148683369910767616201648996940775488] ![(.leaf 0 (Common.fact 661).pointIds 661), (.leaf 1 (Common.fact 662).pointIds 662), (.leaf 2 (Common.fact 582).pointIds 582), (.leaf 3 (Common.fact 603).pointIds 603), (.leaf 4 (Common.fact 642).pointIds 642), (.leaf 5 (Common.fact 631).pointIds 631), B0294]
theorem treeEq0293 : B0293.tree = HexagonCover.NBand.M6667_6700.SplitData.node0293 := by
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
  · exact treeEq0294

def B0137 : Block := .branch 69 ![2535301200457611724498013258113, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 356986147748353490757864740161378849420050448, 21778071482940061661655974875633165926432, 374144419156711148683370374995130933666600027947072] ![Tip0133_0138, B0293, (.leaf 2 (Common.fact 149).pointIds 149), (.leaf 3 (Common.fact 150).pointIds 150), (.leaf 4 (Common.fact 151).pointIds 151), (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 414).pointIds 414)]
theorem treeEq0137 : B0137.tree = HexagonCover.NBand.M6667_6700.SplitData.node0137 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0293
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0136 : Block := .branch 134 ![2535301200457611724498013258113, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 356986147748353490757864740161378849420050448, 393248, 374144419156711148683370374995130933666600027947072] ![(.leaf 0 (Common.fact 408).pointIds 408), (.leaf 1 (Common.fact 409).pointIds 409), (.leaf 2 (Common.fact 410).pointIds 410), (.leaf 3 (Common.fact 411).pointIds 411), (.leaf 4 (Common.fact 412).pointIds 412), B0137, (.leaf 6 (Common.fact 413).pointIds 413)]
theorem treeEq0136 : B0136.tree = HexagonCover.NBand.M6667_6700.SplitData.node0136 := by
  change Tree.branch (134 : Fin 173) _ = Tree.branch (134 : Fin 173) _
  apply congrArg (Tree.branch (134 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0137
  · rfl

def B0135 : Block := .branch 137 ![2535301200457611724498013258113, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 356811923176489970264571492362373784095784976, 393248, 374144419156711148683370374995130933666600027947072] ![(.leaf 0 (Common.fact 402).pointIds 402), (.leaf 1 (Common.fact 403).pointIds 403), (.leaf 2 (Common.fact 404).pointIds 404), (.leaf 3 (Common.fact 405).pointIds 405), B0136, (.leaf 5 (Common.fact 406).pointIds 406), (.leaf 6 (Common.fact 407).pointIds 407)]
theorem treeEq0135 : B0135.tree = HexagonCover.NBand.M6667_6700.SplitData.node0135 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0136
  · rfl
  · rfl

def B0134 : Block := .branch 143 ![2535301200457611724498013258113, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 356811923176489970264571492362373784095784976, 393248, 374144419156711148683370374995130933666600027947072] ![(.leaf 0 (Common.fact 396).pointIds 396), (.leaf 1 (Common.fact 397).pointIds 397), (.leaf 2 (Common.fact 398).pointIds 398), (.leaf 3 (Common.fact 399).pointIds 399), (.leaf 4 (Common.fact 400).pointIds 400), B0135, (.leaf 6 (Common.fact 401).pointIds 401)]
theorem treeEq0134 : B0134.tree = HexagonCover.NBand.M6667_6700.SplitData.node0134 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0135
  · rfl

def B0133 : Block := .branch 148 ![2535301200457611724498013258113, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 98320, 393248, 374144419156711148683370374995130933666600027947072] ![(.leaf 0 (Common.fact 390).pointIds 390), (.leaf 1 (Common.fact 391).pointIds 391), (.leaf 2 (Common.fact 392).pointIds 392), (.leaf 3 (Common.fact 393).pointIds 393), B0134, (.leaf 5 (Common.fact 394).pointIds 394), (.leaf 6 (Common.fact 395).pointIds 395)]
theorem treeEq0133 : B0133.tree = HexagonCover.NBand.M6667_6700.SplitData.node0133 := by
  change Tree.branch (148 : Fin 173) _ = Tree.branch (148 : Fin 173) _
  apply congrArg (Tree.branch (148 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0134
  · rfl
  · rfl

theorem accepted0133 : B0133.accepted = true := by decide +kernel
theorem checked0133 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0133 (maskNeeds ![2535301200457611724498013258113, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 98320, 393248, 374144419156711148683370374995130933666600027947072]) := by
  rw [← treeEq0133]
  exact B0133.sound accepted0133
#print axioms checked0133

def B0342 : Block := .branch 133 ![385, 1538, 6148, 24584, 98320, 187072209578355573530071658587684226515959365894176, 374144419164877923869098054149002959764198505578560] ![(.leaf 0 (Common.fact 174).pointIds 174), (.leaf 1 (Common.fact 175).pointIds 175), (.leaf 2 (Common.fact 176).pointIds 176), (.leaf 3 (Common.fact 177).pointIds 177), (.leaf 4 (Common.fact 178).pointIds 178), (.leaf 5 (Common.fact 361).pointIds 361), (.leaf 6 (Common.fact 701).pointIds 701)]
theorem treeEq0342 : B0342.tree = HexagonCover.NBand.M6667_6700.SplitData.node0342 := by
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
  · rfl

def B0341 : Block := .branch 167 ![2475880079723682054405095809, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 664613997892457936451903530140270608, 393248, 374144419164877923869098054149002959764198505578560] ![(.leaf 0 (Common.fact 698).pointIds 698), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 262).pointIds 262), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 699).pointIds 699), B0342, (.leaf 6 (Common.fact 700).pointIds 700)]
theorem treeEq0341 : B0341.tree = HexagonCover.NBand.M6667_6700.SplitData.node0341 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0342
  · rfl

def B0340 : Block := .branch 168 ![2475880079723682054405095809, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 664613997892457936451903530140270608, 21778071482940061661655974875633165926432, 8166776808954736973634506732279774576704] ![(.leaf 0 (Common.fact 695).pointIds 695), (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 310).pointIds 310), (.leaf 4 (Common.fact 696).pointIds 696), (.leaf 5 (Common.fact 697).pointIds 697), B0341]
theorem treeEq0340 : B0340.tree = HexagonCover.NBand.M6667_6700.SplitData.node0340 := by
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
  · exact treeEq0341

def B0339 : Block := .branch 131 ![2475880079723682054405095809, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 356812264123470889095492892188884746004168720, 21778071482940061661655974875633165926432, 5444517873587229265927509872825628885056] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 694).pointIds 694), (.leaf 5 (Common.fact 148).pointIds 148), B0340]
theorem treeEq0339 : B0339.tree = HexagonCover.NBand.M6667_6700.SplitData.node0339 := by
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
  · exact treeEq0340

def B0338 : Block := .branch 121 ![2475880079723682054405095809, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 356812264123470889095492892188884746004168720, 21778071482940061661655974875633165926432, 5444517873587229265927509872825628885056] ![(.leaf 0 (Common.fact 426).pointIds 426), (.leaf 1 (Common.fact 427).pointIds 427), (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), (.leaf 4 (Common.fact 693).pointIds 693), (.leaf 5 (Common.fact 430).pointIds 430), B0339]
theorem treeEq0338 : B0338.tree = HexagonCover.NBand.M6667_6700.SplitData.node0338 := by
  change Tree.branch (121 : Fin 173) _ = Tree.branch (121 : Fin 173) _
  apply congrArg (Tree.branch (121 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0339

def B0337 : Block := .branch 119 ![2475880079723682054405095809, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 356812263458856891203034955736981215863996432, 21778071482940061661655974875633165926432, 5444517873587693493442241890428716056640] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), B0338, (.leaf 5 (Common.fact 419).pointIds 419), (.leaf 6 (Common.fact 692).pointIds 692)]
theorem treeEq0337 : B0337.tree = HexagonCover.NBand.M6667_6700.SplitData.node0337 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0338
  · rfl
  · rfl

def B0336 : Block := .branch 129 ![2475880079723682054405095809, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 356812263458856891203034955736981215863996432, 21778071482940061661655974875633165926432, 5444517873587693493442241890428716056640] ![(.leaf 0 (Common.fact 555).pointIds 555), (.leaf 1 (Common.fact 556).pointIds 556), (.leaf 2 (Common.fact 557).pointIds 557), (.leaf 3 (Common.fact 558).pointIds 558), B0337, (.leaf 5 (Common.fact 559).pointIds 559), (.leaf 6 (Common.fact 691).pointIds 691)]
theorem treeEq0336 : B0336.tree = HexagonCover.NBand.M6667_6700.SplitData.node0336 := by
  change Tree.branch (129 : Fin 173) _ = Tree.branch (129 : Fin 173) _
  apply congrArg (Tree.branch (129 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0337
  · rfl
  · rfl

def B0335 : Block := .branch 134 ![2475880079723682054405095809, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 356812263458856891203034955736981215863996432, 393248, 5444517873587693493442241890428716056640] ![(.leaf 0 (Common.fact 408).pointIds 408), (.leaf 1 (Common.fact 409).pointIds 409), (.leaf 2 (Common.fact 410).pointIds 410), (.leaf 3 (Common.fact 411).pointIds 411), (.leaf 4 (Common.fact 412).pointIds 412), B0336, (.leaf 6 (Common.fact 690).pointIds 690)]
theorem treeEq0335 : B0335.tree = HexagonCover.NBand.M6667_6700.SplitData.node0335 := by
  change Tree.branch (134 : Fin 173) _ = Tree.branch (134 : Fin 173) _
  apply congrArg (Tree.branch (134 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0336
  · rfl

def B0334 : Block := .branch 139 ![2475880079723682054405095809, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 356812263458856891203034955736981215863996432, 393248, 5444517873587693493442241890428716056640] ![(.leaf 0 (Common.fact 684).pointIds 684), (.leaf 1 (Common.fact 685).pointIds 685), (.leaf 2 (Common.fact 686).pointIds 686), (.leaf 3 (Common.fact 687).pointIds 687), B0335, (.leaf 5 (Common.fact 688).pointIds 688), (.leaf 6 (Common.fact 689).pointIds 689)]
theorem treeEq0334 : B0334.tree = HexagonCover.NBand.M6667_6700.SplitData.node0334 := by
  change Tree.branch (139 : Fin 173) _ = Tree.branch (139 : Fin 173) _
  apply congrArg (Tree.branch (139 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0335
  · rfl
  · rfl

def B0333 : Block := .branch 132 ![2475880079723682054405095809, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 356812263458856891203034955736981215863996432, 393248, 2852678078028248171520424673344] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 683).pointIds 683), (.leaf 5 (Common.fact 142).pointIds 142), B0334]
theorem treeEq0333 : B0333.tree = HexagonCover.NBand.M6667_6700.SplitData.node0333 := by
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
  · exact treeEq0334

def B0332 : Block := .branch 128 ![2475880079723682054405095809, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 356811923176489970264571492362373784095784976, 393248, 1300926892711735155304144506978368] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), B0333, (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 682).pointIds 682)]
theorem treeEq0332 : B0332.tree = HexagonCover.NBand.M6667_6700.SplitData.node0332 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0333
  · rfl
  · rfl

def B0331 : Block := .branch 137 ![2475880079723682054405095809, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 356811923176489970264571492362373784095784976, 393248, 1300926892711735155304144506978368] ![(.leaf 0 (Common.fact 402).pointIds 402), (.leaf 1 (Common.fact 403).pointIds 403), (.leaf 2 (Common.fact 404).pointIds 404), (.leaf 3 (Common.fact 405).pointIds 405), B0332, (.leaf 5 (Common.fact 406).pointIds 406), (.leaf 6 (Common.fact 681).pointIds 681)]
theorem treeEq0331 : B0331.tree = HexagonCover.NBand.M6667_6700.SplitData.node0331 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0332
  · rfl
  · rfl

def B0330 : Block := .branch 138 ![2475880079723682054405095809, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 356811923176489970264571492362373784095784976, 393248, 1300926892711735155304144506978368] ![(.leaf 0 (Common.fact 643).pointIds 643), (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 645).pointIds 645), (.leaf 3 (Common.fact 646).pointIds 646), B0331, (.leaf 5 (Common.fact 647).pointIds 647), (.leaf 6 (Common.fact 680).pointIds 680)]
theorem treeEq0330 : B0330.tree = HexagonCover.NBand.M6667_6700.SplitData.node0330 := by
  change Tree.branch (138 : Fin 173) _ = Tree.branch (138 : Fin 173) _
  apply congrArg (Tree.branch (138 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0331
  · rfl
  · rfl

def B0329 : Block := .branch 143 ![2475880079723682054405095809, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 356811923176489970264571492362373784095784976, 393248, 1300926892711735155304144506978368] ![(.leaf 0 (Common.fact 396).pointIds 396), (.leaf 1 (Common.fact 397).pointIds 397), (.leaf 2 (Common.fact 398).pointIds 398), (.leaf 3 (Common.fact 399).pointIds 399), (.leaf 4 (Common.fact 400).pointIds 400), B0330, (.leaf 6 (Common.fact 679).pointIds 679)]
theorem treeEq0329 : B0329.tree = HexagonCover.NBand.M6667_6700.SplitData.node0329 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0330
  · rfl

def B0328 : Block := .branch 148 ![2475880079723682054405095809, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 98320, 393248, 1300926892711735155304144506978368] ![(.leaf 0 (Common.fact 390).pointIds 390), (.leaf 1 (Common.fact 391).pointIds 391), (.leaf 2 (Common.fact 392).pointIds 392), (.leaf 3 (Common.fact 393).pointIds 393), B0329, (.leaf 5 (Common.fact 394).pointIds 394), (.leaf 6 (Common.fact 678).pointIds 678)]
theorem treeEq0328 : B0328.tree = HexagonCover.NBand.M6667_6700.SplitData.node0328 := by
  change Tree.branch (148 : Fin 173) _ = Tree.branch (148 : Fin 173) _
  apply congrArg (Tree.branch (148 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0329
  · rfl
  · rfl

theorem accepted0328 : B0328.accepted = true := by decide +kernel
theorem checked0328 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0328 (maskNeeds ![2475880079723682054405095809, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 98320, 393248, 1300926892711735155304144506978368]) := by
  rw [← treeEq0328]
  exact B0328.sound accepted0328
#print axioms checked0328

def B0356 : Block := .branch 133 ![385, 1538, 6148, 24584, 98320, 187072209578355573530071658587684226515959365894176, 374144419164877923866565228828625071721754897416256] ![(.leaf 0 (Common.fact 174).pointIds 174), (.leaf 1 (Common.fact 175).pointIds 175), (.leaf 2 (Common.fact 176).pointIds 176), (.leaf 3 (Common.fact 177).pointIds 177), (.leaf 4 (Common.fact 178).pointIds 178), (.leaf 5 (Common.fact 361).pointIds 361), (.leaf 6 (Common.fact 716).pointIds 716)]
theorem treeEq0356 : B0356.tree = HexagonCover.NBand.M6667_6700.SplitData.node0356 := by
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
  · rfl

def B0355 : Block := .branch 167 ![1208926972536133781553537, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 664613997892457936451903530140270608, 393248, 374144419164877923866565228828625071721754897416256] ![(.leaf 0 (Common.fact 714).pointIds 714), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 262).pointIds 262), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 699).pointIds 699), B0356, (.leaf 6 (Common.fact 715).pointIds 715)]
theorem treeEq0355 : B0355.tree = HexagonCover.NBand.M6667_6700.SplitData.node0355 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0356
  · rfl

def B0354 : Block := .branch 168 ![1208926972536133781553537, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 664613997892457936451903530140270608, 21778071482940061661655974875633165926432, 8166776806421911653256618689836166414400] ![(.leaf 0 (Common.fact 713).pointIds 713), (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 310).pointIds 310), (.leaf 4 (Common.fact 696).pointIds 696), (.leaf 5 (Common.fact 697).pointIds 697), B0355]
theorem treeEq0354 : B0354.tree = HexagonCover.NBand.M6667_6700.SplitData.node0354 := by
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
  · exact treeEq0355

def B0353 : Block := .branch 119 ![1208926972536133781553537, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 98320, 21778071482940061661655974875633165926432, 8166778104496281029468436494994611109952] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), B0354, (.leaf 5 (Common.fact 419).pointIds 419), (.leaf 6 (Common.fact 712).pointIds 712)]
theorem treeEq0353 : B0353.tree = HexagonCover.NBand.M6667_6700.SplitData.node0353 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0354
  · rfl
  · rfl

def B0352 : Block := .branch 131 ![1208926972536133781553537, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 1020847100762815390390123822295304732688, 21778071482940061661655974875633165926432, 5444519169128773321761439635540465418304] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 711).pointIds 711), (.leaf 5 (Common.fact 148).pointIds 148), B0353]
theorem treeEq0352 : B0352.tree = HexagonCover.NBand.M6667_6700.SplitData.node0352 := by
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
  · exact treeEq0353

def B0351 : Block := .branch 128 ![1208926972536133781553537, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 680564733841876926926749214863536521232, 21778071482940061661655974875633165926432, 5444519169128773321761439635540465418304] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), B0352, (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 710).pointIds 710)]
theorem treeEq0351 : B0351.tree = HexagonCover.NBand.M6667_6700.SplitData.node0351 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0352
  · rfl
  · rfl

def B0350 : Block := .branch 134 ![1208926972536133781553537, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 680564733841876926926749214863536521232, 393248, 5444519169128773321761439635540465418304] ![(.leaf 0 (Common.fact 408).pointIds 408), (.leaf 1 (Common.fact 409).pointIds 409), (.leaf 2 (Common.fact 410).pointIds 410), (.leaf 3 (Common.fact 411).pointIds 411), (.leaf 4 (Common.fact 412).pointIds 412), B0351, (.leaf 6 (Common.fact 709).pointIds 709)]
theorem treeEq0350 : B0350.tree = HexagonCover.NBand.M6667_6700.SplitData.node0350 := by
  change Tree.branch (134 : Fin 173) _ = Tree.branch (134 : Fin 173) _
  apply congrArg (Tree.branch (134 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0351
  · rfl

def B0349 : Block := .branch 132 ![1208926972536133781553537, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 680564733841876926926749214863536521232, 393248, 1298393757906347445916632174035008] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 708).pointIds 708), (.leaf 5 (Common.fact 142).pointIds 142), B0350]
theorem treeEq0349 : B0349.tree = HexagonCover.NBand.M6667_6700.SplitData.node0349 := by
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
  · exact treeEq0350

def B0348 : Block := .branch 129 ![1208926972536133781553537, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 98320, 393248, 1298393757906347445916632174035008] ![(.leaf 0 (Common.fact 555).pointIds 555), (.leaf 1 (Common.fact 556).pointIds 556), (.leaf 2 (Common.fact 557).pointIds 557), (.leaf 3 (Common.fact 558).pointIds 558), B0349, (.leaf 5 (Common.fact 559).pointIds 559), (.leaf 6 (Common.fact 707).pointIds 707)]
theorem treeEq0348 : B0348.tree = HexagonCover.NBand.M6667_6700.SplitData.node0348 := by
  change Tree.branch (129 : Fin 173) _ = Tree.branch (129 : Fin 173) _
  apply congrArg (Tree.branch (129 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0349
  · rfl
  · rfl

def B0347 : Block := .branch 137 ![1208926972536133781553537, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 98320, 393248, 1298393757906347445916632174035008] ![(.leaf 0 (Common.fact 402).pointIds 402), (.leaf 1 (Common.fact 403).pointIds 403), (.leaf 2 (Common.fact 404).pointIds 404), (.leaf 3 (Common.fact 405).pointIds 405), B0348, (.leaf 5 (Common.fact 406).pointIds 406), (.leaf 6 (Common.fact 706).pointIds 706)]
theorem treeEq0347 : B0347.tree = HexagonCover.NBand.M6667_6700.SplitData.node0347 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0348
  · rfl
  · rfl

def B0346 : Block := .branch 138 ![1208926972536133781553537, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 98320, 393248, 1298393757906347445916632174035008] ![(.leaf 0 (Common.fact 643).pointIds 643), (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 645).pointIds 645), (.leaf 3 (Common.fact 646).pointIds 646), B0347, (.leaf 5 (Common.fact 647).pointIds 647), (.leaf 6 (Common.fact 705).pointIds 705)]
theorem treeEq0346 : B0346.tree = HexagonCover.NBand.M6667_6700.SplitData.node0346 := by
  change Tree.branch (138 : Fin 173) _ = Tree.branch (138 : Fin 173) _
  apply congrArg (Tree.branch (138 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0347
  · rfl
  · rfl

def B0345 : Block := .branch 139 ![1208926972536133781553537, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 98320, 393248, 1298393757906347445916632174035008] ![(.leaf 0 (Common.fact 684).pointIds 684), (.leaf 1 (Common.fact 685).pointIds 685), (.leaf 2 (Common.fact 686).pointIds 686), (.leaf 3 (Common.fact 687).pointIds 687), B0346, (.leaf 5 (Common.fact 688).pointIds 688), (.leaf 6 (Common.fact 704).pointIds 704)]
theorem treeEq0345 : B0345.tree = HexagonCover.NBand.M6667_6700.SplitData.node0345 := by
  change Tree.branch (139 : Fin 173) _ = Tree.branch (139 : Fin 173) _
  apply congrArg (Tree.branch (139 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0346
  · rfl
  · rfl

def B0344 : Block := .branch 143 ![1208926972536133781553537, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 98320, 393248, 1298393757906347445916632174035008] ![(.leaf 0 (Common.fact 396).pointIds 396), (.leaf 1 (Common.fact 397).pointIds 397), (.leaf 2 (Common.fact 398).pointIds 398), (.leaf 3 (Common.fact 399).pointIds 399), (.leaf 4 (Common.fact 400).pointIds 400), B0345, (.leaf 6 (Common.fact 703).pointIds 703)]
theorem treeEq0344 : B0344.tree = HexagonCover.NBand.M6667_6700.SplitData.node0344 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0345
  · rfl

def B0343 : Block := .branch 148 ![1208926972536133781553537, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 98320, 393248, 1298393757906347445916632174035008] ![(.leaf 0 (Common.fact 390).pointIds 390), (.leaf 1 (Common.fact 391).pointIds 391), (.leaf 2 (Common.fact 392).pointIds 392), (.leaf 3 (Common.fact 393).pointIds 393), B0344, (.leaf 5 (Common.fact 394).pointIds 394), (.leaf 6 (Common.fact 702).pointIds 702)]
theorem treeEq0343 : B0343.tree = HexagonCover.NBand.M6667_6700.SplitData.node0343 := by
  change Tree.branch (148 : Fin 173) _ = Tree.branch (148 : Fin 173) _
  apply congrArg (Tree.branch (148 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0344
  · rfl
  · rfl

theorem accepted0343 : B0343.accepted = true := by decide +kernel
theorem checked0343 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0343 (maskNeeds ![1208926972536133781553537, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 98320, 393248, 1298393757906347445916632174035008]) := by
  rw [← treeEq0343]
  exact B0343.sound accepted0343
#print axioms checked0343

def Tip0024_0030 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0030 ![2535301201047907534856718909825, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 393248, 8166776807053725300806894647637806940224] HexagonCover.NBand.M6667_6700.SplitTree.Run0001.checked0030
def Tip0024_0133 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0133 ![2535301200457611724498013258113, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 98320, 393248, 374144419156711148683370374995130933666600027947072] checked0133
def Tip0024_0328 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0328 ![2475880079723682054405095809, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 98320, 393248, 1300926892711735155304144506978368] checked0328
def Tip0024_0343 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0343 ![1208926972536133781553537, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 98320, 393248, 1298393757906347445916632174035008] checked0343
def B0131 : Block := .branch 169 ![2535301200457611724498013258113, 618970609938501595666843138, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 393248, 374144419170322441737298077848970316025182115332160] ![(.leaf 0 (Common.fact 387).pointIds 387), (.leaf 1 (Common.fact 388).pointIds 388), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 353).pointIds 353), (.leaf 4 (Common.fact 376).pointIds 376), (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 333).pointIds 333)]
theorem treeEq0131 : B0131.tree = HexagonCover.NBand.M6667_6700.SplitData.node0131 := by
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

def B0130 : Block := .branch 133 ![2535301200457611724498013258113, 618970609938501595666843138, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 187072209578355573530071658587684226515959365894176, 374144419159433405995828047018142328587365532565568] ![(.leaf 0 (Common.fact 174).pointIds 174), (.leaf 1 (Common.fact 175).pointIds 175), (.leaf 2 (Common.fact 176).pointIds 176), (.leaf 3 (Common.fact 177).pointIds 177), (.leaf 4 (Common.fact 178).pointIds 178), (.leaf 5 (Common.fact 361).pointIds 361), B0131]
theorem treeEq0130 : B0130.tree = HexagonCover.NBand.M6667_6700.SplitData.node0130 := by
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
  · exact treeEq0131

def B0129 : Block := .branch 167 ![2535301200457611724498013258113, 618970609938501595666843138, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 393248, 374144419164877923867196887733670437007022175551552] ![(.leaf 0 (Common.fact 384).pointIds 384), (.leaf 1 (Common.fact 385).pointIds 385), (.leaf 2 (Common.fact 262).pointIds 262), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 374).pointIds 374), B0130, (.leaf 6 (Common.fact 386).pointIds 386)]
theorem treeEq0129 : B0129.tree = HexagonCover.NBand.M6667_6700.SplitData.node0129 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0130
  · rfl

def B0128 : Block := .branch 168 ![2535301200457611724498013258113, 618970609938501595666843138, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 393248, 8166776807053570558301983975103444549696] ![(.leaf 0 (Common.fact 382).pointIds 382), (.leaf 1 (Common.fact 383).pointIds 383), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 310).pointIds 310), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 318).pointIds 318), B0129]
theorem treeEq0128 : B0128.tree = HexagonCover.NBand.M6667_6700.SplitData.node0128 := by
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
  · exact treeEq0129

def B0029 : Block := .branch 69 ![2535301200457611724498013258113, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 393248, 8166776807053725300806894647637806940224] ![Tip0024_0030, B0128, (.leaf 2 (Common.fact 149).pointIds 149), (.leaf 3 (Common.fact 150).pointIds 150), (.leaf 4 (Common.fact 151).pointIds 151), (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 153).pointIds 153)]
theorem treeEq0029 : B0029.tree = HexagonCover.NBand.M6667_6700.SplitData.node0029 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0128
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0028 : Block := .branch 131 ![2535301200457611724498013258113, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 393248, 5444517871686217593099897788183661248576] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 147).pointIds 147), (.leaf 5 (Common.fact 148).pointIds 148), B0029]
theorem treeEq0028 : B0028.tree = HexagonCover.NBand.M6667_6700.SplitData.node0028 := by
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
  · exact treeEq0029

def B0027 : Block := .branch 132 ![2535301200457611724498013258113, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 393248, 951202177685904069275369865280] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 141).pointIds 141), (.leaf 5 (Common.fact 142).pointIds 142), B0028]
theorem treeEq0027 : B0027.tree = HexagonCover.NBand.M6667_6700.SplitData.node0027 := by
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
  · exact treeEq0028

def B0132 : Block := .branch 168 ![2535301200457611724498013258113, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 98320, 393248, 1623227057819762480634681296945216] ![(.leaf 0 (Common.fact 382).pointIds 382), (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 310).pointIds 310), (.leaf 4 (Common.fact 389).pointIds 389), (.leaf 5 (Common.fact 318).pointIds 318), Tip0024_0133]
theorem treeEq0132 : B0132.tree = HexagonCover.NBand.M6667_6700.SplitData.node0132 := by
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

def B0026 : Block := .branch 108 ![2535301200457611724498013258113, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 98320, 393248, 1299025416811392811201899452170304] ![(.leaf 0 (Common.fact 132).pointIds 132), (.leaf 1 (Common.fact 133).pointIds 133), (.leaf 2 (Common.fact 134).pointIds 134), (.leaf 3 (Common.fact 135).pointIds 135), B0027, (.leaf 5 (Common.fact 136).pointIds 136), B0132]
theorem treeEq0026 : B0026.tree = HexagonCover.NBand.M6667_6700.SplitData.node0026 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0027
  · rfl
  · exact treeEq0132

def B0025 : Block := .branch 101 ![2475880079723682054405095809, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 98320, 393248, 1299025416811392811201899452170304] ![B0026, (.leaf 1 (Common.fact 127).pointIds 127), (.leaf 2 (Common.fact 128).pointIds 128), (.leaf 3 (Common.fact 129).pointIds 129), (.leaf 4 (Common.fact 130).pointIds 130), (.leaf 5 (Common.fact 131).pointIds 131), Tip0024_0328]
theorem treeEq0025 : B0025.tree = HexagonCover.NBand.M6667_6700.SplitData.node0025 := by
  change Tree.branch (101 : Fin 173) _ = Tree.branch (101 : Fin 173) _
  apply congrArg (Tree.branch (101 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0026
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0024 : Block := .branch 91 ![1208926972536133781553537, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 98320, 393248, 1299025416811392811201899452170304] ![B0025, (.leaf 1 (Common.fact 122).pointIds 122), (.leaf 2 (Common.fact 123).pointIds 123), (.leaf 3 (Common.fact 124).pointIds 124), (.leaf 4 (Common.fact 125).pointIds 125), (.leaf 5 (Common.fact 126).pointIds 126), Tip0024_0343]
theorem treeEq0024 : B0024.tree = HexagonCover.NBand.M6667_6700.SplitData.node0024 := by
  change Tree.branch (91 : Fin 173) _ = Tree.branch (91 : Fin 173) _
  apply congrArg (Tree.branch (91 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0025
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0024 : B0024.accepted = true := by decide +kernel
theorem checked0024 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0024 (maskNeeds ![1208926972536133781553537, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 98320, 393248, 1299025416811392811201899452170304]) := by
  rw [← treeEq0024]
  exact B0024.sound accepted0024
#print axioms checked0024

def Tip0023_0024 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0024 ![1208926972536133781553537, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 98320, 393248, 1299025416811392811201899452170304] checked0024
def B0365 : Block := .branch 167 ![1208926972536133781553537, 302231454904756805305858, 77919046967349146032132, 77371252455336267181219848, 2993155710065612352971116801974439986629133943799824, 1496577676626844588240573268701473812127674924400672, 1122433257470133441180747483146182059136817573658688] ![(.leaf 0 (Common.fact 714).pointIds 714), (.leaf 1 (Common.fact 736).pointIds 736), (.leaf 2 (Common.fact 262).pointIds 262), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 737).pointIds 737), (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 739).pointIds 739)]
theorem treeEq0365 : B0365.tree = HexagonCover.NBand.M6667_6700.SplitData.node0365 := by
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

def B0364 : Block := .branch 170 ![1208926972536133781553537, 302231454904756805305858, 77919046967349146032132, 77371252455336267181219848, 2993155710239836924834637295267687785634199268065296, 393248, 1122433257470133441180747483146182059136817573658688] ![(.leaf 0 (Common.fact 732).pointIds 732), (.leaf 1 (Common.fact 733).pointIds 733), (.leaf 2 (Common.fact 497).pointIds 497), (.leaf 3 (Common.fact 519).pointIds 519), (.leaf 4 (Common.fact 734).pointIds 734), B0365, (.leaf 6 (Common.fact 735).pointIds 735)]
theorem treeEq0364 : B0364.tree = HexagonCover.NBand.M6667_6700.SplitData.node0364 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0365
  · rfl

def B0363 : Block := .branch 169 ![1208926972536133781553537, 302231454904756805305858, 77919046967349146032132, 77371252455336267181219848, 2993155710239836924834637295267687785634199268065296, 11150372599265311570767859136324180753383456, 374144419156711147060460848795445153072980111654976] ![(.leaf 0 (Common.fact 728).pointIds 728), (.leaf 1 (Common.fact 729).pointIds 729), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 353).pointIds 353), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 731).pointIds 731), B0364]
theorem treeEq0363 : B0363.tree = HexagonCover.NBand.M6667_6700.SplitData.node0363 := by
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
  · exact treeEq0364

def B0362 : Block := .branch 171 ![1208926972536133781553537, 302231454904756805305858, 77919046967349146032132, 77371252455336267181219848, 356986147748353490757864740161378849420050448, 11150372599265311570767859136324180753383456, 374144419156711148358535218171656970878138556350528] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 725).pointIds 725), (.leaf 2 (Common.fact 499).pointIds 499), (.leaf 3 (Common.fact 539).pointIds 539), B0363, (.leaf 5 (Common.fact 726).pointIds 726), (.leaf 6 (Common.fact 727).pointIds 727)]
theorem treeEq0362 : B0362.tree = HexagonCover.NBand.M6667_6700.SplitData.node0362 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0363
  · rfl
  · rfl

def B0361 : Block := .branch 134 ![1208926972536133781553537, 302231454904756805305858, 77919046967349146032132, 77371252455336267181219848, 356986147748353490757864740161378849420050448, 11150372599265311570767859136324180753383456, 374144419156711148358535218171656970878138556350528] ![(.leaf 0 (Common.fact 408).pointIds 408), (.leaf 1 (Common.fact 409).pointIds 409), (.leaf 2 (Common.fact 410).pointIds 410), (.leaf 3 (Common.fact 411).pointIds 411), (.leaf 4 (Common.fact 412).pointIds 412), B0362, (.leaf 6 (Common.fact 723).pointIds 723)]
theorem treeEq0361 : B0361.tree = HexagonCover.NBand.M6667_6700.SplitData.node0361 := by
  change Tree.branch (134 : Fin 173) _ = Tree.branch (134 : Fin 173) _
  apply congrArg (Tree.branch (134 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0362
  · rfl

def B0360 : Block := .branch 148 ![1208926972536133781553537, 302231454904756805305858, 77919046967349146032132, 77371252455336267181219848, 174224571863520493293247799005065324363792, 11150372599265311570767859136324180753383456, 374144419156711148358535218171656970878138556350528] ![(.leaf 0 (Common.fact 390).pointIds 390), (.leaf 1 (Common.fact 391).pointIds 391), (.leaf 2 (Common.fact 392).pointIds 392), (.leaf 3 (Common.fact 393).pointIds 393), B0361, (.leaf 5 (Common.fact 394).pointIds 394), (.leaf 6 (Common.fact 722).pointIds 722)]
theorem treeEq0360 : B0360.tree = HexagonCover.NBand.M6667_6700.SplitData.node0360 := by
  change Tree.branch (148 : Fin 173) _ = Tree.branch (148 : Fin 173) _
  apply congrArg (Tree.branch (148 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0361
  · rfl
  · rfl

def B0359 : Block := .branch 168 ![1208926972536133781553537, 302231454904756805305858, 77919046967349146032132, 77371252455336267181219848, 174224571863520493293247799005065324363792, 11150372599265311570767859136324180753383456, 1298391900996288517846219825348672] ![(.leaf 0 (Common.fact 713).pointIds 713), (.leaf 1 (Common.fact 719).pointIds 719), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 310).pointIds 310), (.leaf 4 (Common.fact 720).pointIds 720), (.leaf 5 (Common.fact 721).pointIds 721), B0360]
theorem treeEq0359 : B0359.tree = HexagonCover.NBand.M6667_6700.SplitData.node0359 := by
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
  · exact treeEq0360

def B0358 : Block := .branch 137 ![1208926972536133781553537, 302231454904756805305858, 77919046967349146032132, 96714065569170333976518664, 98320, 11150372599265311570767859136324180753383456, 1298391900996288517846219825348672] ![(.leaf 0 (Common.fact 402).pointIds 402), (.leaf 1 (Common.fact 403).pointIds 403), (.leaf 2 (Common.fact 404).pointIds 404), (.leaf 3 (Common.fact 405).pointIds 405), B0359, (.leaf 5 (Common.fact 406).pointIds 406), (.leaf 6 (Common.fact 718).pointIds 718)]
theorem treeEq0358 : B0358.tree = HexagonCover.NBand.M6667_6700.SplitData.node0358 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0359
  · rfl
  · rfl

def B0357 : Block := .branch 143 ![1208926972536133781553537, 302231454904756805305858, 77919046967349146032132, 96714065569170333976518664, 98320, 393248, 1298391900996288517846219825348672] ![(.leaf 0 (Common.fact 396).pointIds 396), (.leaf 1 (Common.fact 397).pointIds 397), (.leaf 2 (Common.fact 398).pointIds 398), (.leaf 3 (Common.fact 399).pointIds 399), (.leaf 4 (Common.fact 400).pointIds 400), B0358, (.leaf 6 (Common.fact 717).pointIds 717)]
theorem treeEq0357 : B0357.tree = HexagonCover.NBand.M6667_6700.SplitData.node0357 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0358
  · rfl

def B0023 : Block := .branch 89 ![1208926972536133781553537, 302231454904756805305858, 77919046967349146032132, 96714065569170333976518664, 98320, 393248, 1299025416811392811201899452170304] ![(.leaf 0 (Common.fact 117).pointIds 117), Tip0023_0024, (.leaf 2 (Common.fact 118).pointIds 118), (.leaf 3 (Common.fact 119).pointIds 119), (.leaf 4 (Common.fact 120).pointIds 120), (.leaf 5 (Common.fact 121).pointIds 121), B0357]
theorem treeEq0023 : B0023.tree = HexagonCover.NBand.M6667_6700.SplitData.node0023 := by
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
  · exact treeEq0357

theorem accepted0023 : B0023.accepted = true := by decide +kernel
theorem checked0023 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0023 (maskNeeds ![1208926972536133781553537, 302231454904756805305858, 77919046967349146032132, 96714065569170333976518664, 98320, 393248, 1299025416811392811201899452170304]) := by
  rw [← treeEq0023]
  exact B0023.sound accepted0023
#print axioms checked0023

end HexagonCover.NBand.M6667_6700.SplitTree.Run0004
