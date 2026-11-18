import HexagonCover.NBand.M7300_7500.SplitData
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7300_7500.SplitTree.Run0069
open OwnerTree HexagonCover.NBand.M7300_7500

abbrev Block := Chunk (n := 172) (Certificate := Fin 1033) (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck

def B4940 : Block := .branch 121 ![385, 1538, 6148, 24584, 324518553658426726783156020674576, 393248, 397528445375783665234659403553046924245505110704192] ![(.leaf 0 (Common.fact 735).pointIds 735), (.leaf 1 (Common.fact 736).pointIds 736), (.leaf 2 (Common.fact 737).pointIds 737), (.leaf 3 (Common.fact 738).pointIds 738), (.leaf 4 (Common.fact 739).pointIds 739), (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 741).pointIds 741)]
theorem treeEq4940 : B4940.tree = HexagonCover.NBand.M7300_7500.SplitData.node4940 := by
  change Tree.branch (121 : Fin 172) _ = Tree.branch (121 : Fin 172) _
  apply congrArg (Tree.branch (121 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4939 : Block := .branch 168 ![748288838313464829418687052859126286692759839441281, 618970019642690137449563650, 18446745173221185540, 38685626227668133590622216, 324518553658426726783156020674576, 393248, 23384026219072518174516086377678471213586379702336] ![(.leaf 0 (Common.fact 734).pointIds 734), (.leaf 1 (Common.fact 1017).pointIds 1017), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), B4940]
theorem treeEq4939 : B4939.tree = HexagonCover.NBand.M7300_7500.SplitData.node4939 := by
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
  · exact treeEq4940

def B4938 : Block := .branch 125 ![748288838313422294122821935551193364866830868414849, 618970019642690137449563650, 18446745173221185540, 38685626227668133590622216, 324518553658426726783156020674576, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516395862688292558655104483392] ![B4939, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 940).pointIds 940)]
theorem treeEq4938 : B4938.tree = HexagonCover.NBand.M7300_7500.SplitData.node4938 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4939
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4937 : Block := .branch 164 ![748288838313422294122821935551193364866830868414849, 618970019642690137449563650, 18446745173221185540, 38685626227668133590622216, 324518553658426726783156020674576, 1496577676626844588240573268701473812127674924400672, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 680).pointIds 680), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B4938]
theorem treeEq4937 : B4937.tree = HexagonCover.NBand.M7300_7500.SplitData.node4937 := by
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
  · exact treeEq4938

def B4936 : Block := .branch 169 ![2535301200456458802993406411137, 618970019786805325525419522, 18446745173221185540, 38685626227668133590622216, 324518553658426726783156020674576, 1496577676626844588240573268701473812127674924400672, 21778071483257438539227764244160183795776] ![B4937, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq4936 : B4936.tree = HexagonCover.NBand.M7300_7500.SplitData.node4936 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4937
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4935 : Block := .branch 170 ![2535301200456458802993406411137, 618970019786805325525419522, 18446745173221185540, 38685626227668133590622216, 324518553658426726783156020674576, 393248, 21778071483891263839341878944908535398464] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 679).pointIds 679), B4936, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq4935 : B4935.tree = HexagonCover.NBand.M7300_7500.SplitData.node4935 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4936
  · rfl

def B4948 : Block := .branch 124 ![1267650600228229401496703205761, 1538, 6148, 24584, 98320, 393248, 2993155353275467248288605616950545057932291876585536] ![(.leaf 0 (Common.fact 815).pointIds 815), (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), (.leaf 4 (Common.fact 214).pointIds 214), (.leaf 5 (Common.fact 215).pointIds 215), (.leaf 6 (Common.fact 816).pointIds 816)]
theorem treeEq4948 : B4948.tree = HexagonCover.NBand.M7300_7500.SplitData.node4948 := by
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

def B4947 : Block := .branch 100 ![385, 1461501637330902918204303802735925709793382106626, 6148, 24584, 98320, 393248, 2993155353275467248288605616950545057932291876585536] ![B4948, (.leaf 1 (Common.fact 941).pointIds 941), (.leaf 2 (Common.fact 433).pointIds 433), (.leaf 3 (Common.fact 434).pointIds 434), (.leaf 4 (Common.fact 435).pointIds 435), (.leaf 5 (Common.fact 436).pointIds 436), (.leaf 6 (Common.fact 814).pointIds 814)]
theorem treeEq4947 : B4947.tree = HexagonCover.NBand.M7300_7500.SplitData.node4947 := by
  change Tree.branch (100 : Fin 172) _ = Tree.branch (100 : Fin 172) _
  apply congrArg (Tree.branch (100 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4948
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4946 : Block := .branch 160 ![385, 618970019642690137449563650, 18446745173221185540, 24584, 98320, 393248, 2993155353275467248288605616950545057932291876585536] ![(.leaf 0 (Common.fact 285).pointIds 285), B4947, (.leaf 2 (Common.fact 914).pointIds 914), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 813).pointIds 813)]
theorem treeEq4946 : B4946.tree = HexagonCover.NBand.M7300_7500.SplitData.node4946 := by
  change Tree.branch (160 : Fin 172) _ = Tree.branch (160 : Fin 172) _
  apply congrArg (Tree.branch (160 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq4947
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4945 : Block := .branch 162 ![385, 618970019642690137449563650, 18446745173221185540, 24584, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467248288605616950545057932291876585536] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), B4946, (.leaf 4 (Common.fact 658).pointIds 658), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 746).pointIds 746)]
theorem treeEq4945 : B4945.tree = HexagonCover.NBand.M7300_7500.SplitData.node4945 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4946
  · rfl
  · rfl
  · rfl

def B4944 : Block := .branch 171 ![385, 618970019786805325525419522, 18446745173221185540, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 21778071807459079547597433676942028570688] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 656).pointIds 656), B4945]
theorem treeEq4944 : B4944.tree = HexagonCover.NBand.M7300_7500.SplitData.node4944 := by
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
  · exact treeEq4945

def B4943 : Block := .branch 170 ![385, 618970019786805325525419522, 18446745173221185540, 38685626227668133590622216, 98320, 42535295865117307932921825928971419680, 21778071808409817497768605728064555974720] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), B4944, (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq4943 : B4943.tree = HexagonCover.NBand.M7300_7500.SplitData.node4943 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4944
  · rfl
  · rfl

def B4942 : Block := .branch 125 ![374144419156711147062678618375824911834912137412993, 618970019786805325525419522, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071808409817497768605728064555974720] ![(.leaf 0 (Common.fact 410).pointIds 410), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B4943, (.leaf 6 (Common.fact 940).pointIds 940)]
theorem treeEq4942 : B4942.tree = HexagonCover.NBand.M7300_7500.SplitData.node4942 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4943
  · rfl

def B4941 : Block := .branch 168 ![2535301200456458802993406411137, 618970019786805325525419522, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071808409817497768605728064555974720] ![B4942, (.leaf 1 (Common.fact 1017).pointIds 1017), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 480).pointIds 480)]
theorem treeEq4941 : B4941.tree = HexagonCover.NBand.M7300_7500.SplitData.node4941 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4942
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4934 : Block := .branch 108 ![2535301200456458802993406411137, 618970019786805325525419522, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483891263839341878944908535398464] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), B4935, (.leaf 5 (Common.fact 308).pointIds 308), B4941]
theorem treeEq4934 : B4934.tree = HexagonCover.NBand.M7300_7500.SplitData.node4934 := by
  change Tree.branch (108 : Fin 172) _ = Tree.branch (108 : Fin 172) _
  apply congrArg (Tree.branch (108 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4935
  · rfl
  · exact treeEq4941

theorem accepted4934 : B4934.accepted = true := by decide +kernel
theorem checked4934 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node4934 (maskNeeds ![2535301200456458802993406411137, 618970019786805325525419522, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483891263839341878944908535398464]) := by
  rw [← treeEq4934]
  exact B4934.sound accepted4934
#print axioms checked4934

def B4982 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 2993155359177324619840843309373372790427570873139216, 393248, 13153514757756197747091530488703775456269751025728] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), (.leaf 4 (Common.fact 875).pointIds 875), (.leaf 5 (Common.fact 151).pointIds 151), (.leaf 6 (Common.fact 876).pointIds 876)]
theorem treeEq4982 : B4982.tree = HexagonCover.NBand.M7300_7500.SplitData.node4982 := by
  change Tree.branch (119 : Fin 172) _ = Tree.branch (119 : Fin 172) _
  apply congrArg (Tree.branch (119 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4981 : Block := .branch 90 ![748288838313422294120286634350736906063837462004097, 374144419156711147060143317478190203745934730331650, 6148, 38685626227668133590622216, 2993155359177324619840843309373372790427570873139216, 393248, 13153514757756197747090292548664490075994851901504] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 1020).pointIds 1020), (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), (.leaf 4 (Common.fact 430).pointIds 430), (.leaf 5 (Common.fact 431).pointIds 431), B4982]
theorem treeEq4981 : B4981.tree = HexagonCover.NBand.M7300_7500.SplitData.node4981 := by
  change Tree.branch (90 : Fin 172) _ = Tree.branch (90 : Fin 172) _
  apply congrArg (Tree.branch (90 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4982

def B4980 : Block := .branch 118 ![748288838313422294120286634350736906063837462004097, 374144419156711147060143317478190203745934730331650, 6148, 38685626227668133590622216, 2993155359177324619840843309373372790427570873139216, 393248, 13153514757756197748358562118912362167629004668992] ![(.leaf 0 (Common.fact 267).pointIds 267), (.leaf 1 (Common.fact 268).pointIds 268), (.leaf 2 (Common.fact 269).pointIds 269), B4981, (.leaf 4 (Common.fact 871).pointIds 871), (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 6 (Common.fact 872).pointIds 872)]
theorem treeEq4980 : B4980.tree = HexagonCover.NBand.M7300_7500.SplitData.node4980 := by
  change Tree.branch (118 : Fin 172) _ = Tree.branch (118 : Fin 172) _
  apply congrArg (Tree.branch (118 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4981
  · rfl
  · rfl
  · rfl

def B4979 : Block := .branch 100 ![748288838313422294120286634350736906063837462004097, 374144419156711147060143317478190203745934730331650, 6148, 38685626227668133590622216, 2993155359177324619840843309373372790427570873139216, 393248, 13153514757756197747090911518684132766132301463616] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 1019).pointIds 1019), (.leaf 2 (Common.fact 433).pointIds 433), (.leaf 3 (Common.fact 434).pointIds 434), (.leaf 4 (Common.fact 435).pointIds 435), (.leaf 5 (Common.fact 436).pointIds 436), B4980]
theorem treeEq4979 : B4979.tree = HexagonCover.NBand.M7300_7500.SplitData.node4979 := by
  change Tree.branch (100 : Fin 172) _ = Tree.branch (100 : Fin 172) _
  apply congrArg (Tree.branch (100 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4980

def B4978 : Block := .branch 168 ![748288838313464829416151751658669827889766433030529, 302821750714015999329794, 18446745173221185540, 38685626227668133590622216, 2993155359177324619840843309373372790427570873139216, 393248, 13153514757756197747090911518684132766132301463616] ![(.leaf 0 (Common.fact 605).pointIds 605), B4979, (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 868).pointIds 868)]
theorem treeEq4978 : B4978.tree = HexagonCover.NBand.M7300_7500.SplitData.node4978 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq4979
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4977 : Block := .branch 163 ![748288838313464829416151751658669827889766433030529, 302821750714015999329794, 18446745173221185540, 38685626227668133590622216, 2993155359177324619840843309373372790427570873139216, 393248, 1461501659108974401461432856953868608884841119808] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 867).pointIds 867), (.leaf 5 (Common.fact 248).pointIds 248), B4978]
theorem treeEq4977 : B4977.tree = HexagonCover.NBand.M7300_7500.SplitData.node4977 := by
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
  · exact treeEq4978

def B4976 : Block := .branch 165 ![748288838313464829416151751658669827889766433030529, 302821750714015999329794, 18446745173221185540, 38685626227668133590622216, 2993155359177324619840843309373372790427570873139216, 393248, 1461501659108974401461432856953868608884841119808] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 866).pointIds 866), B4977, (.leaf 0 [] 0)]
theorem treeEq4976 : B4976.tree = HexagonCover.NBand.M7300_7500.SplitData.node4976 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4977
  · rfl

def B4975 : Block := .branch 167 ![748288838313464829416151751658669827889766433030529, 302821750714015999329794, 18446745173221185540, 38685626227668133590622216, 2993155359177324619840843309373372790427570873139216, 393248, 1461501659108974401461432856953868608884841119808] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 865).pointIds 865), B4976, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq4975 : B4975.tree = HexagonCover.NBand.M7300_7500.SplitData.node4975 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4976
  · rfl

def B4974 : Block := .branch 142 ![748288838313464829416151751658669827889766433030529, 302821750714015999329794, 18446745173221185540, 38685626227668133590622216, 2993155353602138320208187523989443222265480496644112, 393248, 24845527856403421092720390180414396923379761807424] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B4975, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 864).pointIds 864)]
theorem treeEq4974 : B4974.tree = HexagonCover.NBand.M7300_7500.SplitData.node4974 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4975
  · rfl
  · rfl

def B4973 : Block := .branch 160 ![748288838313464829416151751658669827889766433030529, 302821750714015999329794, 18446745173221185540, 38685626227668133590622216, 2993155353602138320208187523989443222265480496644112, 393248, 23384026219072518174516705347698113903723829264448] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 1018).pointIds 1018), (.leaf 2 (Common.fact 914).pointIds 914), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), B4974]
theorem treeEq4973 : B4973.tree = HexagonCover.NBand.M7300_7500.SplitData.node4973 := by
  change Tree.branch (160 : Fin 172) _ = Tree.branch (160 : Fin 172) _
  apply congrArg (Tree.branch (160 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4974

def B4984 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692015886240373161957371353695048238292648689680, 393248, 23384026219072518174516086378268767023945085354048] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 607).pointIds 607), (.leaf 5 (Common.fact 197).pointIds 197), (.leaf 6 (Common.fact 878).pointIds 878)]
theorem treeEq4984 : B4984.tree = HexagonCover.NBand.M7300_7500.SplitData.node4984 := by
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

def B4983 : Block := .branch 163 ![385, 1538, 6148, 24584, 2787593149816327892691964784081045188345872, 393248, 23384026219072518174516086378268767023945085354048] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B4984, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 877).pointIds 877)]
theorem treeEq4983 : B4983.tree = HexagonCover.NBand.M7300_7500.SplitData.node4983 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4984
  · rfl
  · rfl

def B4972 : Block := .branch 69 ![748288838313464829416151751658669827889766433030529, 302231454903657293678082, 18446745173221185540, 38685626227668133590622216, 2993155356389731470024515416681408006346525684891664, 393248, 23384026219072518174516705347698113903723829264448] ![(.leaf 0 (Common.fact 753).pointIds 753), B4973, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), B4983]
theorem treeEq4972 : B4972.tree = HexagonCover.NBand.M7300_7500.SplitData.node4972 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq4973
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4983

def B4971 : Block := .branch 138 ![748288838313464829416151751658669827889766433030529, 302231454903657293678082, 18446745173221185540, 79266848140492005727134572552, 2993155356041282326297474430094912408336395036360720, 393248, 23384026219072518174516705347698113903723829264448] ![(.leaf 0 (Common.fact 110).pointIds 110), (.leaf 1 (Common.fact 111).pointIds 111), (.leaf 2 (Common.fact 112).pointIds 112), (.leaf 3 (Common.fact 113).pointIds 113), B4972, (.leaf 5 (Common.fact 114).pointIds 114), (.leaf 6 (Common.fact 591).pointIds 591)]
theorem treeEq4971 : B4971.tree = HexagonCover.NBand.M7300_7500.SplitData.node4971 := by
  change Tree.branch (138 : Fin 172) _ = Tree.branch (138 : Fin 172) _
  apply congrArg (Tree.branch (138 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4972
  · rfl
  · rfl

def B4970 : Block := .branch 141 ![748288838313464829416151751658669827889766433030529, 302231454903657293678082, 18446745173221185540, 79266848140492005727134572552, 2993155353253689176481146537402947624255349848113168, 393248, 23384026219072518174516705347698113903723829264448] ![(.leaf 0 (Common.fact 92).pointIds 92), (.leaf 1 (Common.fact 93).pointIds 93), (.leaf 2 (Common.fact 94).pointIds 94), (.leaf 3 (Common.fact 95).pointIds 95), B4971, (.leaf 5 (Common.fact 96).pointIds 96), (.leaf 6 (Common.fact 588).pointIds 588)]
theorem treeEq4970 : B4970.tree = HexagonCover.NBand.M7300_7500.SplitData.node4970 := by
  change Tree.branch (141 : Fin 172) _ = Tree.branch (141 : Fin 172) _
  apply congrArg (Tree.branch (141 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4971
  · rfl
  · rfl

def B4969 : Block := .branch 125 ![748288838313422294120286634350736906063837462004097, 302231454903657293678082, 18446745173221185540, 79266848140492005727134572552, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 23384026219072518174517014832707935248792554045504] ![B4970, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 940).pointIds 940)]
theorem treeEq4969 : B4969.tree = HexagonCover.NBand.M7300_7500.SplitData.node4969 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4970
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4968 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 302231454903657293678082, 18446745173221185540, 79266848140492005727134572552, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 21778071483258057509247406934297633357888] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B4969]
theorem treeEq4968 : B4968.tree = HexagonCover.NBand.M7300_7500.SplitData.node4968 := by
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
  · exact treeEq4969

def B4967 : Block := .branch 169 ![385, 302231599018845369533954, 18446745173221185540, 79266848140492005727134572552, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 21778071483258057509247406934297633357888] ![B4968, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq4967 : B4967.tree = HexagonCover.NBand.M7300_7500.SplitData.node4967 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4968
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4966 : Block := .branch 170 ![385, 302231599018845369533954, 18446745173221185540, 79266848140492005727134572552, 2993155353253689176481146537402947624255349848113168, 393248, 21778071483891882809361521635045984960576] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B4967, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq4966 : B4966.tree = HexagonCover.NBand.M7300_7500.SplitData.node4966 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4967
  · rfl

def B4965 : Block := .branch 171 ![385, 302231599018845369533954, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483891882809361521635045984960576] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B4966, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 595).pointIds 595)]
theorem treeEq4965 : B4965.tree = HexagonCover.NBand.M7300_7500.SplitData.node4965 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4966
  · rfl
  · rfl

theorem accepted4965 : B4965.accepted = true := by decide +kernel
theorem checked4965 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node4965 (maskNeeds ![385, 302231599018845369533954, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483891882809361521635045984960576]) := by
  rw [← treeEq4965]
  exact B4965.sound accepted4965
#print axioms checked4965

def Tip4931_4934 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node4934 ![2535301200456458802993406411137, 618970019786805325525419522, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483891263839341878944908535398464] checked4934
def Tip4931_4965 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node4965 ![385, 302231599018845369533954, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483891882809361521635045984960576] checked4965
def B4956 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 2993155358828875476113802322786877192417440224608272, 393248, 21778071485792739739684223047153590206528] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 749).pointIds 749), (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 579).pointIds 579)]
theorem treeEq4956 : B4956.tree = HexagonCover.NBand.M7300_7500.SplitData.node4956 := by
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
  · rfl

def B4955 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 397528445375783665237195014238513204393567241896000] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B4956, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 748).pointIds 748)]
theorem treeEq4955 : B4955.tree = HexagonCover.NBand.M7300_7500.SplitData.node4955 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4956
  · rfl
  · rfl

def B4954 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 618970019642690137449563650, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 23384026219072518177051697063144751361648510894144] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 1017).pointIds 1017), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), B4955]
theorem treeEq4954 : B4954.tree = HexagonCover.NBand.M7300_7500.SplitData.node4954 := by
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
  · exact treeEq4955

def B4953 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 618970019642690137449563650, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 23384026219072518177051697063144751361648510894144] ![B4954, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 940).pointIds 940)]
theorem treeEq4953 : B4953.tree = HexagonCover.NBand.M7300_7500.SplitData.node4953 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4954
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4952 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 618970019642690137449563650, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 21778071485792739739684223047153590206528] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B4953]
theorem treeEq4952 : B4952.tree = HexagonCover.NBand.M7300_7500.SplitData.node4952 := by
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
  · exact treeEq4953

def B4951 : Block := .branch 169 ![2475880078570760549798248833, 618970019786805325525419522, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 21778071485792739739684223047153590206528] ![B4952, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq4951 : B4951.tree = HexagonCover.NBand.M7300_7500.SplitData.node4951 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4952
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4950 : Block := .branch 170 ![2475880078570760549798248833, 618970019786805325525419522, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 21778071486426565039798337747901941809216] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B4951, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq4950 : B4950.tree = HexagonCover.NBand.M7300_7500.SplitData.node4950 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4951
  · rfl

def B4949 : Block := .branch 171 ![2475880078570760549798248833, 618970019786805325525419522, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071486426565039798337747901941809216] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B4950, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 747).pointIds 747)]
theorem treeEq4949 : B4949.tree = HexagonCover.NBand.M7300_7500.SplitData.node4949 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4950
  · rfl
  · rfl

def B4933 : Block := .branch 101 ![2475880078570760549798248833, 618970019786805325525419522, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483891263839341878944908535398464] ![Tip4931_4934, (.leaf 1 (Common.fact 403).pointIds 403), (.leaf 2 (Common.fact 404).pointIds 404), (.leaf 3 (Common.fact 405).pointIds 405), (.leaf 4 (Common.fact 406).pointIds 406), (.leaf 5 (Common.fact 407).pointIds 407), B4949]
theorem treeEq4933 : B4933.tree = HexagonCover.NBand.M7300_7500.SplitData.node4933 := by
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
  · exact treeEq4949

def B4964 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 2993155358828875476113802322786877192417440224608272, 393248, 21778071483259604934296513659641257263168] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 749).pointIds 749), (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 586).pointIds 586)]
theorem treeEq4964 : B4964.tree = HexagonCover.NBand.M7300_7500.SplitData.node4964 := by
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
  · rfl

def B4963 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 397528445375783665234661879433125495006054908952640] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B4964, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 751).pointIds 751)]
theorem treeEq4963 : B4963.tree = HexagonCover.NBand.M7300_7500.SplitData.node4963 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4964
  · rfl
  · rfl

def B4962 : Block := .branch 168 ![748288838313464829416151751658669827889766433030529, 618970019642690137449563650, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 23384026219072518174518562257757041974136177950784] ![(.leaf 0 (Common.fact 605).pointIds 605), (.leaf 1 (Common.fact 1017).pointIds 1017), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), B4963]
theorem treeEq4962 : B4962.tree = HexagonCover.NBand.M7300_7500.SplitData.node4962 := by
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
  · exact treeEq4963

def B4961 : Block := .branch 125 ![748288838313422294120286634350736906063837462004097, 618970019642690137449563650, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 23384026219072518174518871742766863319204902731840] ![B4962, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 940).pointIds 940)]
theorem treeEq4961 : B4961.tree = HexagonCover.NBand.M7300_7500.SplitData.node4961 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4962
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4960 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 618970019642690137449563650, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 21778071483259914419306335004709982044224] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B4961]
theorem treeEq4960 : B4960.tree = HexagonCover.NBand.M7300_7500.SplitData.node4960 := by
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
  · exact treeEq4961

def B4959 : Block := .branch 169 ![385, 618970019786805325525419522, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 21778071483259914419306335004709982044224] ![B4960, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq4959 : B4959.tree = HexagonCover.NBand.M7300_7500.SplitData.node4959 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4960
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4958 : Block := .branch 170 ![385, 618970019786805325525419522, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 21778071483893739719420449705458333646912] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B4959, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq4958 : B4958.tree = HexagonCover.NBand.M7300_7500.SplitData.node4958 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4959
  · rfl

def B4957 : Block := .branch 171 ![385, 618970019786805325525419522, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483893739719420449705458333646912] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B4958, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 750).pointIds 750)]
theorem treeEq4957 : B4957.tree = HexagonCover.NBand.M7300_7500.SplitData.node4957 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4958
  · rfl
  · rfl

def B4932 : Block := .branch 91 ![385, 618970019786805325525419522, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483891263839341878944908535398464] ![B4933, (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 320).pointIds 320), (.leaf 5 (Common.fact 321).pointIds 321), B4957]
theorem treeEq4932 : B4932.tree = HexagonCover.NBand.M7300_7500.SplitData.node4932 := by
  change Tree.branch (91 : Fin 172) _ = Tree.branch (91 : Fin 172) _
  apply congrArg (Tree.branch (91 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4933
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4957

def B4931 : Block := .branch 89 ![385, 302231599018845369533954, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483891263839341878944908535398464] ![(.leaf 0 (Common.fact 86).pointIds 86), B4932, (.leaf 2 (Common.fact 88).pointIds 88), (.leaf 3 (Common.fact 89).pointIds 89), (.leaf 4 (Common.fact 90).pointIds 90), (.leaf 5 (Common.fact 91).pointIds 91), Tip4931_4965]
theorem treeEq4931 : B4931.tree = HexagonCover.NBand.M7300_7500.SplitData.node4931 := by
  change Tree.branch (89 : Fin 172) _ = Tree.branch (89 : Fin 172) _
  apply congrArg (Tree.branch (89 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq4932
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted4931 : B4931.accepted = true := by decide +kernel
theorem checked4931 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node4931 (maskNeeds ![385, 302231599018845369533954, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483891263839341878944908535398464]) := by
  rw [← treeEq4931]
  exact B4931.sound accepted4931
#print axioms checked4931

def Tip4930_4931 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node4931 ![385, 302231599018845369533954, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483891263839341878944908535398464] checked4931
def B4996 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692015886240373161957371353695048238292648689680, 393248, 397528445375783665234659326181794468909237929508928] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 607).pointIds 607), (.leaf 5 (Common.fact 197).pointIds 197), (.leaf 6 (Common.fact 630).pointIds 630)]
theorem treeEq4996 : B4996.tree = HexagonCover.NBand.M7300_7500.SplitData.node4996 := by
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

def B4995 : Block := .branch 163 ![385, 1538, 6148, 24584, 2787593149816327892691964784081045188345872, 393248, 397528445375783665234659326181794468909237929508928] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B4996, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 629).pointIds 629)]
theorem treeEq4995 : B4995.tree = HexagonCover.NBand.M7300_7500.SplitData.node4995 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4996
  · rfl
  · rfl

def B4994 : Block := .branch 168 ![748288838313464829416151751658669827889766433030529, 302305241879952131884546, 18446745173221185540, 38685626227668133590622216, 2787593149816327892691964784081045188345872, 393248, 23384026219072518174516009006426015877319198507072] ![(.leaf 0 (Common.fact 605).pointIds 605), (.leaf 1 (Common.fact 1021).pointIds 1021), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), B4995]
theorem treeEq4994 : B4994.tree = HexagonCover.NBand.M7300_7500.SplitData.node4994 := by
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
  · exact treeEq4995

def B5000 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692015886240373161957371353695048238292648689680, 393248, 24845527856403421092719693839142298896975131050048] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 607).pointIds 607), (.leaf 5 (Common.fact 197).pointIds 197), (.leaf 6 (Common.fact 886).pointIds 886)]
theorem treeEq5000 : B5000.tree = HexagonCover.NBand.M7300_7500.SplitData.node5000 := by
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

def B4999 : Block := .branch 163 ![385, 1538, 6148, 24584, 2787593149816327892691964784081045188345872, 393248, 24845527856403421092719693839142298896975131050048] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B5000, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 885).pointIds 885)]
theorem treeEq4999 : B4999.tree = HexagonCover.NBand.M7300_7500.SplitData.node4999 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5000
  · rfl
  · rfl

def B4998 : Block := .branch 160 ![385, 302821750714015999329794, 18446745173221185540, 24584, 2787593149816327892691964784081045188345872, 393248, 23384026219072518174516009006426015877319198507072] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 1018).pointIds 1018), (.leaf 2 (Common.fact 914).pointIds 914), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), B4999]
theorem treeEq4998 : B4998.tree = HexagonCover.NBand.M7300_7500.SplitData.node4998 := by
  change Tree.branch (160 : Fin 172) _ = Tree.branch (160 : Fin 172) _
  apply congrArg (Tree.branch (160 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4999

def B5002 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692015886240373161957371353695048238292648689680, 393248, 23384026219072518174516009007016311687677904158784] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 607).pointIds 607), (.leaf 5 (Common.fact 197).pointIds 197), (.leaf 6 (Common.fact 888).pointIds 888)]
theorem treeEq5002 : B5002.tree = HexagonCover.NBand.M7300_7500.SplitData.node5002 := by
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

def B5001 : Block := .branch 163 ![385, 1538, 6148, 24584, 2787593149816327892691964784081045188345872, 393248, 23384026219072518174516009007016311687677904158784] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B5002, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 887).pointIds 887)]
theorem treeEq5001 : B5001.tree = HexagonCover.NBand.M7300_7500.SplitData.node5001 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5002
  · rfl
  · rfl

def B4997 : Block := .branch 69 ![748288838313422294120286634350736906063837462004097, 302231454903657293678082, 18446745173221185540, 24584, 2787593149816327892691964784081045188345872, 393248, 23384026219072518174516009006426015877319198507072] ![(.leaf 0 (Common.fact 753).pointIds 753), B4998, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), B5001]
theorem treeEq4997 : B4997.tree = HexagonCover.NBand.M7300_7500.SplitData.node4997 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq4998
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5001

def B4993 : Block := .branch 66 ![748288838313464829416151751658669827889766433030529, 302231454903657293678082, 18446745173221185540, 38685626227668133590622216, 2787593149816327892691964784081045188345872, 393248, 23384026219072518174516318491435837222387923288128] ![(.leaf 0 (Common.fact 879).pointIds 879), B4994, B4997, (.leaf 3 (Common.fact 880).pointIds 880), (.leaf 4 (Common.fact 881).pointIds 881), (.leaf 5 (Common.fact 882).pointIds 882), (.leaf 6 (Common.fact 883).pointIds 883)]
theorem treeEq4993 : B4993.tree = HexagonCover.NBand.M7300_7500.SplitData.node4993 := by
  change Tree.branch (66 : Fin 172) _ = Tree.branch (66 : Fin 172) _
  apply congrArg (Tree.branch (66 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq4994
  · exact treeEq4997
  · rfl
  · rfl
  · rfl
  · rfl

def B4992 : Block := .branch 135 ![748288838313464829416151751658669827889766433030529, 302231454903657293678082, 18446745173221185540, 38685626227668133590622216, 2787593149816327892691964784081045188345872, 393248, 23384026219072518174516318491435837222387923288128] ![(.leaf 0 (Common.fact 614).pointIds 614), (.leaf 1 (Common.fact 615).pointIds 615), (.leaf 2 (Common.fact 616).pointIds 616), (.leaf 3 (Common.fact 617).pointIds 617), (.leaf 4 (Common.fact 618).pointIds 618), B4993, (.leaf 6 (Common.fact 619).pointIds 619)]
theorem treeEq4992 : B4992.tree = HexagonCover.NBand.M7300_7500.SplitData.node4992 := by
  change Tree.branch (135 : Fin 172) _ = Tree.branch (135 : Fin 172) _
  apply congrArg (Tree.branch (135 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4993
  · rfl

def B4991 : Block := .branch 138 ![748288838313464829416151751658669827889766433030529, 302231454903657293678082, 18446745173221185540, 79266848140492005727134572552, 2787593149816327892691964784081045188345872, 393248, 23384026219072518174516318491435837222387923288128] ![(.leaf 0 (Common.fact 110).pointIds 110), (.leaf 1 (Common.fact 111).pointIds 111), (.leaf 2 (Common.fact 112).pointIds 112), (.leaf 3 (Common.fact 113).pointIds 113), B4992, (.leaf 5 (Common.fact 114).pointIds 114), (.leaf 6 (Common.fact 613).pointIds 613)]
theorem treeEq4991 : B4991.tree = HexagonCover.NBand.M7300_7500.SplitData.node4991 := by
  change Tree.branch (138 : Fin 172) _ = Tree.branch (138 : Fin 172) _
  apply congrArg (Tree.branch (138 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4992
  · rfl
  · rfl

def B4990 : Block := .branch 141 ![748288838313464829416151751658669827889766433030529, 302231454903657293678082, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 23384026219072518174516318491435837222387923288128] ![(.leaf 0 (Common.fact 92).pointIds 92), (.leaf 1 (Common.fact 93).pointIds 93), (.leaf 2 (Common.fact 94).pointIds 94), (.leaf 3 (Common.fact 95).pointIds 95), B4991, (.leaf 5 (Common.fact 96).pointIds 96), (.leaf 6 (Common.fact 610).pointIds 610)]
theorem treeEq4990 : B4990.tree = HexagonCover.NBand.M7300_7500.SplitData.node4990 := by
  change Tree.branch (141 : Fin 172) _ = Tree.branch (141 : Fin 172) _
  apply congrArg (Tree.branch (141 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4991
  · rfl
  · rfl

def B4989 : Block := .branch 125 ![748288838313422294120286634350736906063837462004097, 302231454903657293678082, 18446745173221185540, 79266848140492005727134572552, 98320, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516473233940747894922285678656] ![B4990, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 940).pointIds 940)]
theorem treeEq4989 : B4989.tree = HexagonCover.NBand.M7300_7500.SplitData.node4989 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4990
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4988 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 302231454903657293678082, 18446745173221185540, 79266848140492005727134572552, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483257515910480219580427364991040] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B4989]
theorem treeEq4988 : B4988.tree = HexagonCover.NBand.M7300_7500.SplitData.node4988 := by
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
  · exact treeEq4989

def B4987 : Block := .branch 169 ![385, 302231599018845369533954, 18446745173221185540, 79266848140492005727134572552, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483257515910480219580427364991040] ![B4988, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq4987 : B4987.tree = HexagonCover.NBand.M7300_7500.SplitData.node4987 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4988
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4986 : Block := .branch 170 ![385, 302231599018845369533954, 18446745173221185540, 79266848140492005727134572552, 2993155353253689176481146537402947624255349848113168, 393248, 21778071483891341210594334281175716593728] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B4987, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq4986 : B4986.tree = HexagonCover.NBand.M7300_7500.SplitData.node4986 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4987
  · rfl

def B4985 : Block := .branch 171 ![385, 302231599018845369533954, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483891341210594334281175716593728] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B4986, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 622).pointIds 622)]
theorem treeEq4985 : B4985.tree = HexagonCover.NBand.M7300_7500.SplitData.node4985 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4986
  · rfl
  · rfl

def B4930 : Block := .branch 86 ![385, 302231599018845369533954, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483891263839341878944908535398464] ![(.leaf 0 (Common.fact 326).pointIds 326), (.leaf 1 (Common.fact 327).pointIds 327), (.leaf 2 (Common.fact 939).pointIds 939), Tip4930_4931, (.leaf 4 (Common.fact 329).pointIds 329), (.leaf 5 (Common.fact 330).pointIds 330), B4985]
theorem treeEq4930 : B4930.tree = HexagonCover.NBand.M7300_7500.SplitData.node4930 := by
  change Tree.branch (86 : Fin 172) _ = Tree.branch (86 : Fin 172) _
  apply congrArg (Tree.branch (86 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4985

theorem accepted4930 : B4930.accepted = true := by decide +kernel
theorem checked4930 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node4930 (maskNeeds ![385, 302231599018845369533954, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483891263839341878944908535398464]) := by
  rw [← treeEq4930]
  exact B4930.sound accepted4930
#print axioms checked4930

end HexagonCover.NBand.M7300_7500.SplitTree.Run0069
