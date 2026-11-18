import HexagonCover.NBand.M7300_7500.SplitData
import HexagonCover.NBand.M7300_7500.SplitTree.Run0037
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7300_7500.SplitTree.Run0038
open OwnerTree HexagonCover.NBand.M7300_7500

abbrev Block := Chunk (n := 172) (Certificate := Fin 1033) (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck

def B2746 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 2993155359177324619840843309373372790427570873139216, 393248, 13153514757756197747091530488703775456269751025728] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), (.leaf 4 (Common.fact 875).pointIds 875), (.leaf 5 (Common.fact 151).pointIds 151), (.leaf 6 (Common.fact 876).pointIds 876)]
theorem treeEq2746 : B2746.tree = HexagonCover.NBand.M7300_7500.SplitData.node2746 := by
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

def B2745 : Block := .branch 90 ![748288838313422294120286634350736906063837462004097, 374144419156711147060143317478190203747034241959426, 6148, 38685626227668133590622216, 2993155359177324619840843309373372790427570873139216, 393248, 13153514757756197747090292548664490075994851901504] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 874).pointIds 874), (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), (.leaf 4 (Common.fact 430).pointIds 430), (.leaf 5 (Common.fact 431).pointIds 431), B2746]
theorem treeEq2745 : B2745.tree = HexagonCover.NBand.M7300_7500.SplitData.node2745 := by
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
  · exact treeEq2746

def B2744 : Block := .branch 118 ![748288838313422294120286634350736906063837462004097, 374144419156711147060143317478190203747034241959426, 6148, 38685626227668133590622216, 2993155359177324619840843309373372790427570873139216, 393248, 13153514757756197748358562118912362167629004668992] ![(.leaf 0 (Common.fact 267).pointIds 267), (.leaf 1 (Common.fact 268).pointIds 268), (.leaf 2 (Common.fact 269).pointIds 269), B2745, (.leaf 4 (Common.fact 871).pointIds 871), (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 6 (Common.fact 872).pointIds 872)]
theorem treeEq2744 : B2744.tree = HexagonCover.NBand.M7300_7500.SplitData.node2744 := by
  change Tree.branch (118 : Fin 172) _ = Tree.branch (118 : Fin 172) _
  apply congrArg (Tree.branch (118 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2745
  · rfl
  · rfl
  · rfl

def B2743 : Block := .branch 100 ![748288838313422294120286634350736906063837462004097, 374144419156711147060143317478190203747034241959426, 6148, 38685626227668133590622216, 2993155359177324619840843309373372790427570873139216, 393248, 13153514757756197747090911518684132766132301463616] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 870).pointIds 870), (.leaf 2 (Common.fact 433).pointIds 433), (.leaf 3 (Common.fact 434).pointIds 434), (.leaf 4 (Common.fact 435).pointIds 435), (.leaf 5 (Common.fact 436).pointIds 436), B2744]
theorem treeEq2743 : B2743.tree = HexagonCover.NBand.M7300_7500.SplitData.node2743 := by
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
  · exact treeEq2744

def B2742 : Block := .branch 168 ![748288838313464829416151751658669827889766433030529, 302821750715115510957570, 18446884811197913092, 38685626227668133590622216, 2993156072801170972820783838516357515175139064512528, 393248, 13153514757756197747090911518684132766132301463616] ![(.leaf 0 (Common.fact 605).pointIds 605), B2743, (.leaf 2 (Common.fact 858).pointIds 858), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 868).pointIds 868)]
theorem treeEq2742 : B2742.tree = HexagonCover.NBand.M7300_7500.SplitData.node2742 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2743
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2741 : Block := .branch 163 ![748288838313464829416151751658669827889766433030529, 302821750715115510957570, 18446884811197913092, 38685626227668133590622216, 2993156072801170972820783838516357515175139064512528, 393248, 1461501659108974401461432856953868608884841119808] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 867).pointIds 867), (.leaf 5 (Common.fact 248).pointIds 248), B2742]
theorem treeEq2741 : B2741.tree = HexagonCover.NBand.M7300_7500.SplitData.node2741 := by
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
  · exact treeEq2742

def B2740 : Block := .branch 165 ![748288838313464829416151751658669827889766433030529, 302821750715115510957570, 18446884811197913092, 38685626227668133590622216, 2993156072801170972820783838516357515175139064512528, 393248, 1461501659108974401461432856953868608884841119808] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 866).pointIds 866), B2741, (.leaf 0 [] 0)]
theorem treeEq2740 : B2740.tree = HexagonCover.NBand.M7300_7500.SplitData.node2740 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2741
  · rfl

def B2739 : Block := .branch 167 ![748288838313464829416151751658669827889766433030529, 302821750715115510957570, 18446884811197913092, 38685626227668133590622216, 2993156072801170972820783838516357515175139064512528, 393248, 1461501659108974401461432856953868608884841119808] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 865).pointIds 865), B2740, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq2739 : B2739.tree = HexagonCover.NBand.M7300_7500.SplitData.node2739 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2740
  · rfl

def B2738 : Block := .branch 142 ![748288838313464829416151751658669827889766433030529, 302821750715115510957570, 18446884811197913092, 38685626227668133590622216, 2993156067225984673188128053132427947013048688017424, 393248, 24845527856403421092720390180414396923379761807424] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B2739, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 864).pointIds 864)]
theorem treeEq2738 : B2738.tree = HexagonCover.NBand.M7300_7500.SplitData.node2738 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2739
  · rfl
  · rfl

def B2737 : Block := .branch 160 ![748288838313464829416151751658669827889766433030529, 302821750715115510957570, 18446884811197913092, 38685626227668133590622216, 2993156067225984673188128053132427947013048688017424, 393248, 23384026219072518174516705347698113903723829264448] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 863).pointIds 863), (.leaf 2 (Common.fact 859).pointIds 859), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), B2738]
theorem treeEq2737 : B2737.tree = HexagonCover.NBand.M7300_7500.SplitData.node2737 := by
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
  · exact treeEq2738

def B2748 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692015886240373161957371353695048238292648689680, 393248, 23384026219072518174516086378268767023945085354048] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 607).pointIds 607), (.leaf 5 (Common.fact 197).pointIds 197), (.leaf 6 (Common.fact 878).pointIds 878)]
theorem treeEq2748 : B2748.tree = HexagonCover.NBand.M7300_7500.SplitData.node2748 := by
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

def B2747 : Block := .branch 163 ![385, 1538, 6148, 24584, 2787593149816327892691964784081045188345872, 393248, 23384026219072518174516086378268767023945085354048] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B2748, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 877).pointIds 877)]
theorem treeEq2747 : B2747.tree = HexagonCover.NBand.M7300_7500.SplitData.node2747 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2748
  · rfl
  · rfl

def B2736 : Block := .branch 69 ![748288838313464829416151751658669827889766433030529, 302231454904756805305858, 18446884811197913092, 38685626227668133590622216, 2993156070013577823004455945824392731094093876264976, 393248, 23384026219072518174516705347698113903723829264448] ![(.leaf 0 (Common.fact 753).pointIds 753), B2737, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), B2747]
theorem treeEq2736 : B2736.tree = HexagonCover.NBand.M7300_7500.SplitData.node2736 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2737
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2747

def B2735 : Block := .branch 138 ![748288838313464829416151751658669827889766433030529, 302231454904756805305858, 18446884811197913092, 79266848140492005727134572552, 2993156069665128679277414959237897133083963227734032, 393248, 23384026219072518174516705347698113903723829264448] ![(.leaf 0 (Common.fact 110).pointIds 110), (.leaf 1 (Common.fact 111).pointIds 111), (.leaf 2 (Common.fact 112).pointIds 112), (.leaf 3 (Common.fact 113).pointIds 113), B2736, (.leaf 5 (Common.fact 114).pointIds 114), (.leaf 6 (Common.fact 591).pointIds 591)]
theorem treeEq2735 : B2735.tree = HexagonCover.NBand.M7300_7500.SplitData.node2735 := by
  change Tree.branch (138 : Fin 172) _ = Tree.branch (138 : Fin 172) _
  apply congrArg (Tree.branch (138 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2736
  · rfl
  · rfl

def B2734 : Block := .branch 141 ![748288838313464829416151751658669827889766433030529, 302231454904756805305858, 18446884811197913092, 79266848140492005727134572552, 2993156066877535529461087066545932349002918039486480, 393248, 23384026219072518174516705347698113903723829264448] ![(.leaf 0 (Common.fact 92).pointIds 92), (.leaf 1 (Common.fact 93).pointIds 93), (.leaf 2 (Common.fact 94).pointIds 94), (.leaf 3 (Common.fact 95).pointIds 95), B2735, (.leaf 5 (Common.fact 96).pointIds 96), (.leaf 6 (Common.fact 588).pointIds 588)]
theorem treeEq2734 : B2734.tree = HexagonCover.NBand.M7300_7500.SplitData.node2734 := by
  change Tree.branch (141 : Fin 172) _ = Tree.branch (141 : Fin 172) _
  apply congrArg (Tree.branch (141 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2735
  · rfl
  · rfl

def B2733 : Block := .branch 125 ![748288838313422294120286634350736906063837462004097, 302231454904756805305858, 18446884811197913092, 79266848140492005727134572552, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 23384026219072518174517014832707935248792554045504] ![B2734, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq2733 : B2733.tree = HexagonCover.NBand.M7300_7500.SplitData.node2733 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2734
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2732 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 302231454904756805305858, 18446884811197913092, 79266848140492005727134572552, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071483258057509247406934297633357888] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2733]
theorem treeEq2732 : B2732.tree = HexagonCover.NBand.M7300_7500.SplitData.node2732 := by
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
  · exact treeEq2733

def B2731 : Block := .branch 169 ![385, 302231599019944881161730, 18446884811197913092, 79266848140492005727134572552, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071483258057509247406934297633357888] ![B2732, (.leaf 1 (Common.fact 850).pointIds 850), (.leaf 2 (Common.fact 851).pointIds 851), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2731 : B2731.tree = HexagonCover.NBand.M7300_7500.SplitData.node2731 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2732
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2730 : Block := .branch 170 ![385, 302231599019944881161730, 18446884811197913092, 79266848140492005727134572552, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483258057509247406934297633357888] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 852).pointIds 852), (.leaf 2 (Common.fact 853).pointIds 853), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B2731, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2730 : B2730.tree = HexagonCover.NBand.M7300_7500.SplitData.node2730 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2731
  · rfl

def B2729 : Block := .branch 171 ![385, 302231599019944881161730, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483258057509247406934297633357888] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 854).pointIds 854), (.leaf 2 (Common.fact 855).pointIds 855), (.leaf 3 (Common.fact 620).pointIds 620), B2730, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 595).pointIds 595)]
theorem treeEq2729 : B2729.tree = HexagonCover.NBand.M7300_7500.SplitData.node2729 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2730
  · rfl
  · rfl

theorem accepted2729 : B2729.accepted = true := by decide +kernel
theorem checked2729 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node2729 (maskNeeds ![385, 302231599019944881161730, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483258057509247406934297633357888]) := by
  rw [← treeEq2729]
  exact B2729.sound accepted2729
#print axioms checked2729

def Tip2695_2698 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node2698 ![2535301200456458802993406411137, 618970019786806425037047298, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] HexagonCover.NBand.M7300_7500.SplitTree.Run0037.checked2698
def Tip2695_2729 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node2729 ![385, 302231599019944881161730, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483258057509247406934297633357888] checked2729
def B2720 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 2993155358828875476113802322786877192417440224608272, 393248, 21778071485792739739684223047153590206528] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 749).pointIds 749), (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 579).pointIds 579)]
theorem treeEq2720 : B2720.tree = HexagonCover.NBand.M7300_7500.SplitData.node2720 := by
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

def B2719 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 397528445375783665237195014238513204393567241896000] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B2720, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 748).pointIds 748)]
theorem treeEq2719 : B2719.tree = HexagonCover.NBand.M7300_7500.SplitData.node2719 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2720
  · rfl
  · rfl

def B2718 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 618970019642691236961191426, 18446884811197913092, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 23384026219072518177051697063144751361648510894144] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 862).pointIds 862), (.leaf 2 (Common.fact 858).pointIds 858), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B2719]
theorem treeEq2718 : B2718.tree = HexagonCover.NBand.M7300_7500.SplitData.node2718 := by
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
  · exact treeEq2719

def B2717 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 618970019642691236961191426, 18446884811197913092, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 23384026219072518177051697063144751361648510894144] ![B2718, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq2717 : B2717.tree = HexagonCover.NBand.M7300_7500.SplitData.node2717 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2718
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2716 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 618970019642691236961191426, 18446884811197913092, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071485792739739684223047153590206528] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2717]
theorem treeEq2716 : B2716.tree = HexagonCover.NBand.M7300_7500.SplitData.node2716 := by
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
  · exact treeEq2717

def B2715 : Block := .branch 169 ![2475880078570760549798248833, 618970019786806425037047298, 18446884811197913092, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071485792739739684223047153590206528] ![B2716, (.leaf 1 (Common.fact 850).pointIds 850), (.leaf 2 (Common.fact 851).pointIds 851), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2715 : B2715.tree = HexagonCover.NBand.M7300_7500.SplitData.node2715 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2716
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2714 : Block := .branch 170 ![2475880078570760549798248833, 618970019786806425037047298, 18446884811197913092, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 21778071485792739739684223047153590206528] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 852).pointIds 852), (.leaf 2 (Common.fact 853).pointIds 853), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B2715, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2714 : B2714.tree = HexagonCover.NBand.M7300_7500.SplitData.node2714 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2715
  · rfl

def B2713 : Block := .branch 171 ![2475880078570760549798248833, 618970019786806425037047298, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071485792739739684223047153590206528] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 854).pointIds 854), (.leaf 2 (Common.fact 855).pointIds 855), (.leaf 3 (Common.fact 620).pointIds 620), B2714, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 747).pointIds 747)]
theorem treeEq2713 : B2713.tree = HexagonCover.NBand.M7300_7500.SplitData.node2713 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2714
  · rfl
  · rfl

def B2697 : Block := .branch 101 ![2475880078570760549798248833, 618970019786806425037047298, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![Tip2695_2698, (.leaf 1 (Common.fact 403).pointIds 403), (.leaf 2 (Common.fact 404).pointIds 404), (.leaf 3 (Common.fact 405).pointIds 405), (.leaf 4 (Common.fact 406).pointIds 406), (.leaf 5 (Common.fact 407).pointIds 407), B2713]
theorem treeEq2697 : B2697.tree = HexagonCover.NBand.M7300_7500.SplitData.node2697 := by
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
  · exact treeEq2713

def B2728 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 2993155358828875476113802322786877192417440224608272, 393248, 21778071483259604934296513659641257263168] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 749).pointIds 749), (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 586).pointIds 586)]
theorem treeEq2728 : B2728.tree = HexagonCover.NBand.M7300_7500.SplitData.node2728 := by
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

def B2727 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 397528445375783665234661879433125495006054908952640] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B2728, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 751).pointIds 751)]
theorem treeEq2727 : B2727.tree = HexagonCover.NBand.M7300_7500.SplitData.node2727 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2728
  · rfl
  · rfl

def B2726 : Block := .branch 168 ![748288838313464829416151751658669827889766433030529, 618970019642691236961191426, 18446884811197913092, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 23384026219072518174518562257757041974136177950784] ![(.leaf 0 (Common.fact 605).pointIds 605), (.leaf 1 (Common.fact 862).pointIds 862), (.leaf 2 (Common.fact 858).pointIds 858), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B2727]
theorem treeEq2726 : B2726.tree = HexagonCover.NBand.M7300_7500.SplitData.node2726 := by
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
  · exact treeEq2727

def B2725 : Block := .branch 125 ![748288838313422294120286634350736906063837462004097, 618970019642691236961191426, 18446884811197913092, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 23384026219072518174518871742766863319204902731840] ![B2726, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq2725 : B2725.tree = HexagonCover.NBand.M7300_7500.SplitData.node2725 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2726
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2724 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 618970019642691236961191426, 18446884811197913092, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071483259914419306335004709982044224] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2725]
theorem treeEq2724 : B2724.tree = HexagonCover.NBand.M7300_7500.SplitData.node2724 := by
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
  · exact treeEq2725

def B2723 : Block := .branch 169 ![385, 618970019786806425037047298, 18446884811197913092, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071483259914419306335004709982044224] ![B2724, (.leaf 1 (Common.fact 850).pointIds 850), (.leaf 2 (Common.fact 851).pointIds 851), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2723 : B2723.tree = HexagonCover.NBand.M7300_7500.SplitData.node2723 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2724
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2722 : Block := .branch 170 ![385, 618970019786806425037047298, 18446884811197913092, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483259914419306335004709982044224] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 852).pointIds 852), (.leaf 2 (Common.fact 853).pointIds 853), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B2723, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2722 : B2722.tree = HexagonCover.NBand.M7300_7500.SplitData.node2722 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2723
  · rfl

def B2721 : Block := .branch 171 ![385, 618970019786806425037047298, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483259914419306335004709982044224] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 854).pointIds 854), (.leaf 2 (Common.fact 855).pointIds 855), (.leaf 3 (Common.fact 620).pointIds 620), B2722, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 750).pointIds 750)]
theorem treeEq2721 : B2721.tree = HexagonCover.NBand.M7300_7500.SplitData.node2721 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2722
  · rfl
  · rfl

def B2696 : Block := .branch 91 ![385, 618970019786806425037047298, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![B2697, (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 320).pointIds 320), (.leaf 5 (Common.fact 321).pointIds 321), B2721]
theorem treeEq2696 : B2696.tree = HexagonCover.NBand.M7300_7500.SplitData.node2696 := by
  change Tree.branch (91 : Fin 172) _ = Tree.branch (91 : Fin 172) _
  apply congrArg (Tree.branch (91 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2697
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2721

def B2695 : Block := .branch 89 ![385, 302231599019944881161730, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 86).pointIds 86), B2696, (.leaf 2 (Common.fact 88).pointIds 88), (.leaf 3 (Common.fact 89).pointIds 89), (.leaf 4 (Common.fact 90).pointIds 90), (.leaf 5 (Common.fact 91).pointIds 91), Tip2695_2729]
theorem treeEq2695 : B2695.tree = HexagonCover.NBand.M7300_7500.SplitData.node2695 := by
  change Tree.branch (89 : Fin 172) _ = Tree.branch (89 : Fin 172) _
  apply congrArg (Tree.branch (89 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2696
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted2695 : B2695.accepted = true := by decide +kernel
theorem checked2695 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node2695 (maskNeeds ![385, 302231599019944881161730, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq2695]
  exact B2695.sound accepted2695
#print axioms checked2695

def Tip2694_2695 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node2695 ![385, 302231599019944881161730, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] checked2695
def B2760 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692015886240373161957371353695048238292648689680, 393248, 397528445375783665234659326181794468909237929508928] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 607).pointIds 607), (.leaf 5 (Common.fact 197).pointIds 197), (.leaf 6 (Common.fact 630).pointIds 630)]
theorem treeEq2760 : B2760.tree = HexagonCover.NBand.M7300_7500.SplitData.node2760 := by
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

def B2759 : Block := .branch 163 ![385, 1538, 6148, 24584, 2787593149816327892691964784081045188345872, 393248, 397528445375783665234659326181794468909237929508928] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B2760, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 629).pointIds 629)]
theorem treeEq2759 : B2759.tree = HexagonCover.NBand.M7300_7500.SplitData.node2759 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2760
  · rfl
  · rfl

def B2758 : Block := .branch 168 ![748288838313464829416151751658669827889766433030529, 302305241881051643512322, 18446884811197913092, 38685626227668133590622216, 716411439502796268421834949508828613379719184, 393248, 23384026219072518174516009006426015877319198507072] ![(.leaf 0 (Common.fact 605).pointIds 605), (.leaf 1 (Common.fact 884).pointIds 884), (.leaf 2 (Common.fact 858).pointIds 858), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B2759]
theorem treeEq2758 : B2758.tree = HexagonCover.NBand.M7300_7500.SplitData.node2758 := by
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
  · exact treeEq2759

def B2764 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692015886240373161957371353695048238292648689680, 393248, 24845527856403421092719693839142298896975131050048] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 607).pointIds 607), (.leaf 5 (Common.fact 197).pointIds 197), (.leaf 6 (Common.fact 886).pointIds 886)]
theorem treeEq2764 : B2764.tree = HexagonCover.NBand.M7300_7500.SplitData.node2764 := by
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

def B2763 : Block := .branch 163 ![385, 1538, 6148, 24584, 2787593149816327892691964784081045188345872, 393248, 24845527856403421092719693839142298896975131050048] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B2764, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 885).pointIds 885)]
theorem treeEq2763 : B2763.tree = HexagonCover.NBand.M7300_7500.SplitData.node2763 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2764
  · rfl
  · rfl

def B2762 : Block := .branch 160 ![385, 302821750715115510957570, 18446884811197913092, 24584, 2787593149816327892691964784081045188345872, 393248, 23384026219072518174516009006426015877319198507072] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 863).pointIds 863), (.leaf 2 (Common.fact 859).pointIds 859), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), B2763]
theorem treeEq2762 : B2762.tree = HexagonCover.NBand.M7300_7500.SplitData.node2762 := by
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
  · exact treeEq2763

def B2766 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692015886240373161957371353695048238292648689680, 393248, 23384026219072518174516009007016311687677904158784] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 607).pointIds 607), (.leaf 5 (Common.fact 197).pointIds 197), (.leaf 6 (Common.fact 888).pointIds 888)]
theorem treeEq2766 : B2766.tree = HexagonCover.NBand.M7300_7500.SplitData.node2766 := by
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

def B2765 : Block := .branch 163 ![385, 1538, 6148, 24584, 2787593149816327892691964784081045188345872, 393248, 23384026219072518174516009007016311687677904158784] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B2766, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 887).pointIds 887)]
theorem treeEq2765 : B2765.tree = HexagonCover.NBand.M7300_7500.SplitData.node2765 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2766
  · rfl
  · rfl

def B2761 : Block := .branch 69 ![748288838313422294120286634350736906063837462004097, 302231454904756805305858, 18446884811197913092, 24584, 2787593149816327892691964784081045188345872, 393248, 23384026219072518174516009006426015877319198507072] ![(.leaf 0 (Common.fact 753).pointIds 753), B2762, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), B2765]
theorem treeEq2761 : B2761.tree = HexagonCover.NBand.M7300_7500.SplitData.node2761 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2762
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2765

def B2757 : Block := .branch 66 ![748288838313464829416151751658669827889766433030529, 302231454904756805305858, 18446884811197913092, 38685626227668133590622216, 716411439502796268421834949508828613379719184, 393248, 23384026219072518174516318491435837222387923288128] ![(.leaf 0 (Common.fact 879).pointIds 879), B2758, B2761, (.leaf 3 (Common.fact 880).pointIds 880), (.leaf 4 (Common.fact 881).pointIds 881), (.leaf 5 (Common.fact 882).pointIds 882), (.leaf 6 (Common.fact 883).pointIds 883)]
theorem treeEq2757 : B2757.tree = HexagonCover.NBand.M7300_7500.SplitData.node2757 := by
  change Tree.branch (66 : Fin 172) _ = Tree.branch (66 : Fin 172) _
  apply congrArg (Tree.branch (66 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2758
  · exact treeEq2761
  · rfl
  · rfl
  · rfl
  · rfl

def B2756 : Block := .branch 135 ![748288838313464829416151751658669827889766433030529, 302231454904756805305858, 18446884811197913092, 38685626227668133590622216, 716411439502796268421834949508828613379719184, 393248, 23384026219072518174516318491435837222387923288128] ![(.leaf 0 (Common.fact 614).pointIds 614), (.leaf 1 (Common.fact 615).pointIds 615), (.leaf 2 (Common.fact 616).pointIds 616), (.leaf 3 (Common.fact 617).pointIds 617), (.leaf 4 (Common.fact 618).pointIds 618), B2757, (.leaf 6 (Common.fact 619).pointIds 619)]
theorem treeEq2756 : B2756.tree = HexagonCover.NBand.M7300_7500.SplitData.node2756 := by
  change Tree.branch (135 : Fin 172) _ = Tree.branch (135 : Fin 172) _
  apply congrArg (Tree.branch (135 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2757
  · rfl

def B2755 : Block := .branch 138 ![748288838313464829416151751658669827889766433030529, 302231454904756805305858, 18446884811197913092, 79266848140492005727134572552, 716411439502796268421834949508828613379719184, 393248, 23384026219072518174516318491435837222387923288128] ![(.leaf 0 (Common.fact 110).pointIds 110), (.leaf 1 (Common.fact 111).pointIds 111), (.leaf 2 (Common.fact 112).pointIds 112), (.leaf 3 (Common.fact 113).pointIds 113), B2756, (.leaf 5 (Common.fact 114).pointIds 114), (.leaf 6 (Common.fact 613).pointIds 613)]
theorem treeEq2755 : B2755.tree = HexagonCover.NBand.M7300_7500.SplitData.node2755 := by
  change Tree.branch (138 : Fin 172) _ = Tree.branch (138 : Fin 172) _
  apply congrArg (Tree.branch (138 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2756
  · rfl
  · rfl

def B2754 : Block := .branch 141 ![748288838313464829416151751658669827889766433030529, 302231454904756805305858, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 23384026219072518174516318491435837222387923288128] ![(.leaf 0 (Common.fact 92).pointIds 92), (.leaf 1 (Common.fact 93).pointIds 93), (.leaf 2 (Common.fact 94).pointIds 94), (.leaf 3 (Common.fact 95).pointIds 95), B2755, (.leaf 5 (Common.fact 96).pointIds 96), (.leaf 6 (Common.fact 610).pointIds 610)]
theorem treeEq2754 : B2754.tree = HexagonCover.NBand.M7300_7500.SplitData.node2754 := by
  change Tree.branch (141 : Fin 172) _ = Tree.branch (141 : Fin 172) _
  apply congrArg (Tree.branch (141 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2755
  · rfl
  · rfl

def B2753 : Block := .branch 125 ![748288838313422294120286634350736906063837462004097, 302231454904756805305858, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516318491435837222387923288128] ![B2754, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq2753 : B2753.tree = HexagonCover.NBand.M7300_7500.SplitData.node2753 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2754
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2752 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 302231454904756805305858, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257361167975308907893002600512] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2753]
theorem treeEq2752 : B2752.tree = HexagonCover.NBand.M7300_7500.SplitData.node2752 := by
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
  · exact treeEq2753

def B2751 : Block := .branch 169 ![385, 302231599019944881161730, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257515910480219580427364991040] ![B2752, (.leaf 1 (Common.fact 850).pointIds 850), (.leaf 2 (Common.fact 851).pointIds 851), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2751 : B2751.tree = HexagonCover.NBand.M7300_7500.SplitData.node2751 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2752
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2750 : Block := .branch 170 ![385, 302231599019944881161730, 18446884811197913092, 79266848140492005727134572552, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257515910480219580427364991040] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 852).pointIds 852), (.leaf 2 (Common.fact 853).pointIds 853), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B2751, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2750 : B2750.tree = HexagonCover.NBand.M7300_7500.SplitData.node2750 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2751
  · rfl

def B2749 : Block := .branch 171 ![385, 302231599019944881161730, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257515910480219580427364991040] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 854).pointIds 854), (.leaf 2 (Common.fact 855).pointIds 855), (.leaf 3 (Common.fact 620).pointIds 620), B2750, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 622).pointIds 622)]
theorem treeEq2749 : B2749.tree = HexagonCover.NBand.M7300_7500.SplitData.node2749 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2750
  · rfl
  · rfl

def B2694 : Block := .branch 86 ![385, 302231599019944881161730, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 326).pointIds 326), (.leaf 1 (Common.fact 327).pointIds 327), (.leaf 2 (Common.fact 856).pointIds 856), Tip2694_2695, (.leaf 4 (Common.fact 329).pointIds 329), (.leaf 5 (Common.fact 330).pointIds 330), B2749]
theorem treeEq2694 : B2694.tree = HexagonCover.NBand.M7300_7500.SplitData.node2694 := by
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
  · exact treeEq2749

theorem accepted2694 : B2694.accepted = true := by decide +kernel
theorem checked2694 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node2694 (maskNeeds ![385, 302231599019944881161730, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq2694]
  exact B2694.sound accepted2694
#print axioms checked2694

def B2797 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275488515612336070444184981120785753571392] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 679).pointIds 679), (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 826).pointIds 826)]
theorem treeEq2797 : B2797.tree = HexagonCover.NBand.M7300_7500.SplitData.node2797 := by
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

def B2796 : Block := .branch 124 ![10385861367669883486462489361645953, 1538, 6148, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467247964403511790218520207821268058176] ![(.leaf 0 (Common.fact 825).pointIds 825), (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), (.leaf 4 (Common.fact 214).pointIds 214), (.leaf 5 (Common.fact 215).pointIds 215), B2797]
theorem treeEq2796 : B2796.tree = HexagonCover.NBand.M7300_7500.SplitData.node2796 := by
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
  · exact treeEq2797

def B2795 : Block := .branch 100 ![10384593717069655257060992658440577, 1461501637330902918203684833011430925934796998146, 6148, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467247964403511790218520207821268058176] ![B2796, (.leaf 1 (Common.fact 823).pointIds 823), (.leaf 2 (Common.fact 433).pointIds 433), (.leaf 3 (Common.fact 434).pointIds 434), (.leaf 4 (Common.fact 435).pointIds 435), (.leaf 5 (Common.fact 436).pointIds 436), (.leaf 6 (Common.fact 824).pointIds 824)]
theorem treeEq2795 : B2795.tree = HexagonCover.NBand.M7300_7500.SplitData.node2795 := by
  change Tree.branch (100 : Fin 172) _ = Tree.branch (100 : Fin 172) _
  apply congrArg (Tree.branch (100 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2796
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2794 : Block := .branch 168 ![10384593717069655257060992658440577, 1461501637330902918203684833011430925934796998146, 18446884811197913092, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 2993155353275467247964403511790218520207821268058176] ![B2795, (.leaf 1 (Common.fact 891).pointIds 891), (.leaf 2 (Common.fact 858).pointIds 858), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 657).pointIds 657)]
theorem treeEq2794 : B2794.tree = HexagonCover.NBand.M7300_7500.SplitData.node2794 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2795
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2793 : Block := .branch 160 ![10384593717069655257060992658440577, 295147906278864455170, 18446884811197913092, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 2993155353275467247964403511790218520207821268058176] ![(.leaf 0 (Common.fact 285).pointIds 285), B2794, (.leaf 2 (Common.fact 859).pointIds 859), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 822).pointIds 822)]
theorem treeEq2793 : B2793.tree = HexagonCover.NBand.M7300_7500.SplitData.node2793 := by
  change Tree.branch (160 : Fin 172) _ = Tree.branch (160 : Fin 172) _
  apply congrArg (Tree.branch (160 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2794
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2792 : Block := .branch 75 ![10384593717069655257060992658440577, 295147906278864455170, 18446884811197913092, 5846006549323611672814778016491359746757320794120, 1496578390250690941220513797844458536875243115479056, 393248, 2993155353275467247964403511790218520207821268058176] ![(.leaf 0 (Common.fact 660).pointIds 660), (.leaf 1 (Common.fact 661).pointIds 661), B2793, (.leaf 3 (Common.fact 662).pointIds 662), (.leaf 4 (Common.fact 663).pointIds 663), (.leaf 5 (Common.fact 664).pointIds 664), (.leaf 6 (Common.fact 665).pointIds 665)]
theorem treeEq2792 : B2792.tree = HexagonCover.NBand.M7300_7500.SplitData.node2792 := by
  change Tree.branch (75 : Fin 172) _ = Tree.branch (75 : Fin 172) _
  apply congrArg (Tree.branch (75 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2793
  · rfl
  · rfl
  · rfl
  · rfl

def B2791 : Block := .branch 162 ![10384593717069655257060992658440577, 295147906278864455170, 18446884811197913092, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 2993155353275467247964403511790218520207821268058176] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), B2792, (.leaf 4 (Common.fact 658).pointIds 658), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 659).pointIds 659)]
theorem treeEq2791 : B2791.tree = HexagonCover.NBand.M7300_7500.SplitData.node2791 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2792
  · rfl
  · rfl
  · rfl

def B2790 : Block := .branch 171 ![10384593717069655257060992658440577, 295292021466940311042, 18446884811197913092, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 854).pointIds 854), (.leaf 2 (Common.fact 855).pointIds 855), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 656).pointIds 656), B2791]
theorem treeEq2790 : B2790.tree = HexagonCover.NBand.M7300_7500.SplitData.node2790 := by
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
  · exact treeEq2791

def B2789 : Block := .branch 170 ![10384593717069655257060992658440577, 295292021466940311042, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 748288838313422294120286634350736906063837462396960, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 852).pointIds 852), (.leaf 2 (Common.fact 853).pointIds 853), (.leaf 3 (Common.fact 623).pointIds 623), B2790, (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2789 : B2789.tree = HexagonCover.NBand.M7300_7500.SplitData.node2789 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2790
  · rfl
  · rfl

def B2788 : Block := .branch 169 ![10384593717070245552871351364092289, 295292021466940311042, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 643).pointIds 643), (.leaf 1 (Common.fact 850).pointIds 850), (.leaf 2 (Common.fact 851).pointIds 851), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 646).pointIds 646), B2789, (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2788 : B2788.tree = HexagonCover.NBand.M7300_7500.SplitData.node2788 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2789
  · rfl

theorem accepted2788 : B2788.accepted = true := by decide +kernel
theorem checked2788 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node2788 (maskNeeds ![10384593717070245552871351364092289, 295292021466940311042, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912]) := by
  rw [← treeEq2788]
  exact B2788.sound accepted2788
#print axioms checked2788

def Tip2787_2788 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node2788 ![10384593717070245552871351364092289, 295292021466940311042, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] checked2788
def B2807 : Block := .branch 142 ![385, 1538, 6148, 24584, 2993338040958355539345921998007037159632806839681040, 393248, 1461501659108974401460659219987178972127352586304] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), (.leaf 4 (Common.fact 895).pointIds 895), (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 896).pointIds 896)]
theorem treeEq2807 : B2807.tree = HexagonCover.NBand.M7300_7500.SplitData.node2807 := by
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

def B2806 : Block := .branch 157 ![385, 1538, 6148, 24584, 2993155353253689176481146537402947624255349848113168, 1496577687777217187505884839469332948451855677390880, 1461501659108974401460659219987178972127352586304] ![(.leaf 0 (Common.fact 175).pointIds 175), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), B2807, (.leaf 5 (Common.fact 700).pointIds 700), (.leaf 0 [] 0)]
theorem treeEq2806 : B2806.tree = HexagonCover.NBand.M7300_7500.SplitData.node2806 := by
  change Tree.branch (157 : Fin 172) _ = Tree.branch (157 : Fin 172) _
  apply congrArg (Tree.branch (157 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2807
  · rfl
  · rfl

def B2805 : Block := .branch 143 ![385, 1538, 6148, 24584, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 1461501659108974401460659219987178972127352586304] ![(.leaf 0 (Common.fact 507).pointIds 507), (.leaf 1 (Common.fact 508).pointIds 508), (.leaf 2 (Common.fact 509).pointIds 509), (.leaf 3 (Common.fact 510).pointIds 510), (.leaf 4 (Common.fact 698).pointIds 698), B2806, (.leaf 6 (Common.fact 894).pointIds 894)]
theorem treeEq2805 : B2805.tree = HexagonCover.NBand.M7300_7500.SplitData.node2805 := by
  change Tree.branch (143 : Fin 172) _ = Tree.branch (143 : Fin 172) _
  apply congrArg (Tree.branch (143 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2806
  · rfl

def B2804 : Block := .branch 125 ![385, 1538, 6148, 24584, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 1461501659108974401460968704997000317196077367360] ![B2805, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq2804 : B2804.tree = HexagonCover.NBand.M7300_7500.SplitData.node2804 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2805
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2803 : Block := .branch 159 ![748288838313422294120289110230815476824387260252545, 737869764047893693954, 6148, 24584, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 1461501659108974401460968704997000317196077367360] ![(.leaf 0 (Common.fact 716).pointIds 716), (.leaf 1 (Common.fact 893).pointIds 893), (.leaf 2 (Common.fact 226).pointIds 226), (.leaf 3 (Common.fact 227).pointIds 227), (.leaf 4 (Common.fact 228).pointIds 228), (.leaf 5 (Common.fact 229).pointIds 229), B2804]
theorem treeEq2803 : B2803.tree = HexagonCover.NBand.M7300_7500.SplitData.node2803 := by
  change Tree.branch (159 : Fin 172) _ = Tree.branch (159 : Fin 172) _
  apply congrArg (Tree.branch (159 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2804

def B2802 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 737869764047893693954, 6148, 24584, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 1461501659108974401460968704997000317196077367360] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2803]
theorem treeEq2802 : B2802.tree = HexagonCover.NBand.M7300_7500.SplitData.node2802 := by
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
  · exact treeEq2803

def B2801 : Block := .branch 169 ![2475880078570760549798248833, 738013879235969549826, 18446884811197913092, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 1461501659108974401461123447501910989730439757888] ![B2802, (.leaf 1 (Common.fact 850).pointIds 850), (.leaf 2 (Common.fact 851).pointIds 851), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2801 : B2801.tree = HexagonCover.NBand.M7300_7500.SplitData.node2801 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2802
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2800 : Block := .branch 170 ![2475880078570760549798248833, 738013879235969549826, 18446884811197913092, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 1461501659108974401461123447501910989730439757888] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 852).pointIds 852), (.leaf 2 (Common.fact 853).pointIds 853), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B2801, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2800 : B2800.tree = HexagonCover.NBand.M7300_7500.SplitData.node2800 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2801
  · rfl

def B2799 : Block := .branch 171 ![2475880078570760549798248833, 738013879235969549826, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 1461501659108974401461123447501910989730439757888] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 854).pointIds 854), (.leaf 2 (Common.fact 855).pointIds 855), (.leaf 3 (Common.fact 620).pointIds 620), B2800, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 822).pointIds 822)]
theorem treeEq2799 : B2799.tree = HexagonCover.NBand.M7300_7500.SplitData.node2799 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2800
  · rfl
  · rfl

def B2798 : Block := .branch 160 ![2475880078570760549798248833, 738013879235969549826, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 892).pointIds 892), (.leaf 2 (Common.fact 859).pointIds 859), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), B2799]
theorem treeEq2798 : B2798.tree = HexagonCover.NBand.M7300_7500.SplitData.node2798 := by
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
  · exact treeEq2799

def B2787 : Block := .branch 69 ![10384596192949733827821542456689025, 442865974056616723970, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![Tip2787_2788, B2798, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq2787 : B2787.tree = HexagonCover.NBand.M7300_7500.SplitData.node2787 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2798
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted2787 : B2787.accepted = true := by decide +kernel
theorem checked2787 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node2787 (maskNeeds ![10384596192949733827821542456689025, 442865974056616723970, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912]) := by
  rw [← treeEq2787]
  exact B2787.sound accepted2787
#print axioms checked2787

end HexagonCover.NBand.M7300_7500.SplitTree.Run0038
