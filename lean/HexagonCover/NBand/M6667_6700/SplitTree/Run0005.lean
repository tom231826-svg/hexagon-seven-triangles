import HexagonCover.NBand.M6667_6700.SplitData
import HexagonCover.NBand.M6667_6700.SplitTree.Run0004
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6667_6700.SplitTree.Run0005
open OwnerTree HexagonCover.NBand.M6667_6700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1334) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def B0403 : Block := .branch 167 ![10633823966279326984383377986849603969, 453347182356585452144130, 1461501637330902918203684910635329987005078575108, 340282366920948134869931524465165885448, 5444517870735015415413993718908291481616, 91343863222217173857761132872755126545078943776, 11692013102050047015473017424301060111998769430592] ![(.leaf 0 (Common.fact 799).pointIds 799), (.leaf 1 (Common.fact 800).pointIds 800), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 801).pointIds 801), (.leaf 4 (Common.fact 802).pointIds 802), (.leaf 5 (Common.fact 803).pointIds 803), (.leaf 6 (Common.fact 804).pointIds 804)]
theorem treeEq0403 : B0403.tree = HexagonCover.NBand.M6667_6700.SplitData.node0403 := by
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

def B0402 : Block := .branch 163 ![10633823966279326984383377986849603969, 453347182356585452144130, 1461501637330902918203684910635329987005078575108, 340282366920948134869931524465165885448, 5444517870735015415413993718908291481616, 91343863222217173857761132872755126545078943776, 3402823669843538762570795954751309086784] ![(.leaf 0 (Common.fact 798).pointIds 798), (.leaf 1 (Common.fact 527).pointIds 527), (.leaf 2 (Common.fact 528).pointIds 528), (.leaf 3 (Common.fact 529).pointIds 529), (.leaf 4 (Common.fact 530).pointIds 530), (.leaf 5 (Common.fact 531).pointIds 531), B0403]
theorem treeEq0402 : B0402.tree = HexagonCover.NBand.M6667_6700.SplitData.node0402 := by
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
  · exact treeEq0403

def B0401 : Block := .branch 123 ![1152921504606847361, 453347182356585452144130, 1461501637330902918203684910635329987005078575108, 340282366920948134869931524465165885448, 5444517870735015415413993718908291481616, 91343863222217173857761132872755126545078943776, 3402824967917753396277703087375391391808] ![B0402, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq0401 : B0401.tree = HexagonCover.NBand.M6667_6700.SplitData.node0401 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0402
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0400 : Block := .branch 77 ![1152921504606847361, 302231454904756805305858, 1461501637330902918203684910635329987005078575108, 340282366920948134869931524465165885448, 5444517870735015415413993718908291481616, 91343863222217173857761132872755126545078943776, 3402824967917753396277703087375391391808] ![(.leaf 0 (Common.fact 791).pointIds 791), B0401, (.leaf 2 (Common.fact 792).pointIds 792), (.leaf 3 (Common.fact 793).pointIds 793), (.leaf 4 (Common.fact 794).pointIds 794), (.leaf 5 (Common.fact 795).pointIds 795), (.leaf 6 (Common.fact 796).pointIds 796)]
theorem treeEq0400 : B0400.tree = HexagonCover.NBand.M6667_6700.SplitData.node0400 := by
  change Tree.branch (77 : Fin 173) _ = Tree.branch (77 : Fin 173) _
  apply congrArg (Tree.branch (77 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0401
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0399 : Block := .branch 160 ![1152921504606847361, 302231454904756805305858, 77919046967349146032132, 340282366920948134869931524465165885448, 5444517870735015415413993718908291481616, 91343863222217173857761132872755126545078943776, 3402824967917753396277703087375391391808] ![(.leaf 0 (Common.fact 236).pointIds 236), (.leaf 1 (Common.fact 237).pointIds 237), B0400, (.leaf 3 (Common.fact 789).pointIds 789), (.leaf 4 (Common.fact 238).pointIds 238), (.leaf 5 (Common.fact 239).pointIds 239), (.leaf 6 (Common.fact 790).pointIds 790)]
theorem treeEq0399 : B0399.tree = HexagonCover.NBand.M6667_6700.SplitData.node0399 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0400
  · rfl
  · rfl
  · rfl
  · rfl

def B0398 : Block := .branch 128 ![1152921504606847361, 302231454904756805305858, 77919046967349146032132, 9671406556917033397673992, 2793037667687062908107378777799953479729168, 91343863222217173857761132872755126545078943776, 3402824967917753396277703087375391391808] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), B0399, (.leaf 4 (Common.fact 787).pointIds 787), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 788).pointIds 788)]
theorem treeEq0398 : B0398.tree = HexagonCover.NBand.M6667_6700.SplitData.node0398 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0399
  · rfl
  · rfl
  · rfl

def B0397 : Block := .branch 131 ![1152921504606847361, 302231454904756805305858, 77919046967349146032132, 9671406556917033397673992, 2793037667687062908107378777799953479729168, 91343863222217173857761132872755126545078943776, 680566032550245688570706227921245700160] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 786).pointIds 786), (.leaf 5 (Common.fact 148).pointIds 148), B0398]
theorem treeEq0397 : B0397.tree = HexagonCover.NBand.M6667_6700.SplitData.node0397 := by
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
  · exact treeEq0398

def B0396 : Block := .branch 156 ![1152921504606847361, 302231454904756805305858, 77919046967349146032132, 9671406556917033397673992, 2793037667687062908107378777799953479729168, 10889035741470030830827987437816583159840, 680566032550245688570706227921245700160] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 785).pointIds 785), B0397, (.leaf 0 [] 0)]
theorem treeEq0396 : B0396.tree = HexagonCover.NBand.M6667_6700.SplitData.node0396 := by
  change Tree.branch (156 : Fin 173) _ = Tree.branch (156 : Fin 173) _
  apply congrArg (Tree.branch (156 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0397
  · rfl

def B0395 : Block := .branch 166 ![1152921504606847361, 302231454904756805305858, 77919046967349146032132, 9671406556917033397673992, 2793037667687062908107378777799953479729168, 10889035741470030830827987437816583159840, 680566032550245688570706227921245700160] ![(.leaf 0 (Common.fact 300).pointIds 300), (.leaf 1 (Common.fact 301).pointIds 301), (.leaf 2 (Common.fact 302).pointIds 302), (.leaf 3 (Common.fact 303).pointIds 303), (.leaf 4 (Common.fact 784).pointIds 784), B0396, (.leaf 6 (Common.fact 305).pointIds 305)]
theorem treeEq0395 : B0395.tree = HexagonCover.NBand.M6667_6700.SplitData.node0395 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0396
  · rfl

def B0394 : Block := .branch 132 ![1152921504606847361, 302231454904756805305858, 77919046967349146032132, 9671406556917033397673992, 2787593149816327892691964784081045188345872, 10889035741470030830827987437816583159840, 680566032550245688570706227921245700160] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), B0395, (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 783).pointIds 783)]
theorem treeEq0394 : B0394.tree = HexagonCover.NBand.M6667_6700.SplitData.node0394 := by
  change Tree.branch (132 : Fin 173) _ = Tree.branch (132 : Fin 173) _
  apply congrArg (Tree.branch (132 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0395
  · rfl
  · rfl

def B0393 : Block := .branch 117 ![1152921504606847361, 302231454904756805305858, 77919046967349146032132, 9671406556917033397673992, 2787593149816327892691964784081045188345872, 10889035741470030830827987437816583159840, 680566032550245688570706227921245700160] ![(.leaf 0 (Common.fact 777).pointIds 777), (.leaf 1 (Common.fact 778).pointIds 778), (.leaf 2 (Common.fact 779).pointIds 779), B0394, (.leaf 4 (Common.fact 780).pointIds 780), (.leaf 5 (Common.fact 781).pointIds 781), (.leaf 6 (Common.fact 782).pointIds 782)]
theorem treeEq0393 : B0393.tree = HexagonCover.NBand.M6667_6700.SplitData.node0393 := by
  change Tree.branch (117 : Fin 173) _ = Tree.branch (117 : Fin 173) _
  apply congrArg (Tree.branch (117 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0394
  · rfl
  · rfl
  · rfl

def B0392 : Block := .branch 129 ![1152921504606847361, 302231454904756805305858, 77919046967349146032132, 9671406556917033397673992, 2787593149816327892691964784081045188345872, 10889035741470030830827987437816583159840, 1298708368761643957013057709277248] ![(.leaf 0 (Common.fact 555).pointIds 555), (.leaf 1 (Common.fact 556).pointIds 556), (.leaf 2 (Common.fact 557).pointIds 557), (.leaf 3 (Common.fact 558).pointIds 558), (.leaf 4 (Common.fact 776).pointIds 776), (.leaf 5 (Common.fact 559).pointIds 559), B0393]
theorem treeEq0392 : B0392.tree = HexagonCover.NBand.M6667_6700.SplitData.node0392 := by
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
  · exact treeEq0393

def B0391 : Block := .branch 130 ![1152921504606847361, 302231454904756805305858, 77919046967349146032132, 9671406556917033397673992, 2787593149816327892691964784081045188345872, 10889035741470030830827987437816583159840, 1298708368761643957013057709277248] ![(.leaf 0 (Common.fact 169).pointIds 169), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 775).pointIds 775), (.leaf 5 (Common.fact 173).pointIds 173), B0392]
theorem treeEq0391 : B0391.tree = HexagonCover.NBand.M6667_6700.SplitData.node0391 := by
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
  · exact treeEq0392

def B0390 : Block := .branch 162 ![1152921504606847361, 302231454904756805305858, 77919046967349146032132, 9671406556917033397673992, 2787593149816327892691964784081045188345872, 10889035741470030830827987437816583159840, 1298708368761643957013057709277248] ![(.leaf 0 (Common.fact 223).pointIds 223), (.leaf 1 (Common.fact 224).pointIds 224), (.leaf 2 (Common.fact 225).pointIds 225), (.leaf 3 (Common.fact 226).pointIds 226), (.leaf 4 (Common.fact 774).pointIds 774), (.leaf 5 (Common.fact 227).pointIds 227), B0391]
theorem treeEq0390 : B0390.tree = HexagonCover.NBand.M6667_6700.SplitData.node0390 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0391

def B0389 : Block := .branch 164 ![1152921504606847361, 302231454904756805305858, 77919046967349146032132, 9671406556917033397673992, 2787593149816327892691964784081045188345872, 10889035741470030830827987437816583159840, 1298708368761643957013057709277248] ![(.leaf 0 (Common.fact 228).pointIds 228), (.leaf 1 (Common.fact 229).pointIds 229), (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 773).pointIds 773), B0390, (.leaf 0 [] 0)]
theorem treeEq0389 : B0389.tree = HexagonCover.NBand.M6667_6700.SplitData.node0389 := by
  change Tree.branch (164 : Fin 173) _ = Tree.branch (164 : Fin 173) _
  apply congrArg (Tree.branch (164 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0390
  · rfl

def B0388 : Block := .branch 141 ![1152921504606847361, 302231454904756805305858, 77919046967349146032132, 9671406556917033397673992, 98320, 10889035741470030830827987437816583159840, 1298708368761643957013057709277248] ![(.leaf 0 (Common.fact 179).pointIds 179), (.leaf 1 (Common.fact 180).pointIds 180), (.leaf 2 (Common.fact 181).pointIds 181), (.leaf 3 (Common.fact 182).pointIds 182), B0389, (.leaf 5 (Common.fact 184).pointIds 184), (.leaf 6 (Common.fact 772).pointIds 772)]
theorem treeEq0388 : B0388.tree = HexagonCover.NBand.M6667_6700.SplitData.node0388 := by
  change Tree.branch (141 : Fin 173) _ = Tree.branch (141 : Fin 173) _
  apply congrArg (Tree.branch (141 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0389
  · rfl
  · rfl

def B0387 : Block := .branch 121 ![1152921504606847361, 302231454904756805305858, 77919046967349146032132, 9671406556917033397673992, 713623846352979940529142984724747568191471632, 10889035741470030830827987437816583159840, 1298708368761643957013057709277248] ![(.leaf 0 (Common.fact 426).pointIds 426), (.leaf 1 (Common.fact 427).pointIds 427), (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), (.leaf 4 (Common.fact 460).pointIds 460), (.leaf 5 (Common.fact 430).pointIds 430), B0388]
theorem treeEq0387 : B0387.tree = HexagonCover.NBand.M6667_6700.SplitData.node0387 := by
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
  · exact treeEq0388

def B0386 : Block := .branch 149 ![1152921504606847361, 302231454904756805305858, 77919046967349146032132, 9671406556917033397673992, 98320, 10889035741470030830827987437816583159840, 1298708368761643957013057709277248] ![(.leaf 0 (Common.fact 204).pointIds 204), (.leaf 1 (Common.fact 205).pointIds 205), (.leaf 2 (Common.fact 206).pointIds 206), (.leaf 3 (Common.fact 207).pointIds 207), B0387, (.leaf 5 (Common.fact 208).pointIds 208), (.leaf 6 (Common.fact 771).pointIds 771)]
theorem treeEq0386 : B0386.tree = HexagonCover.NBand.M6667_6700.SplitData.node0386 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0387
  · rfl
  · rfl

def B0385 : Block := .branch 133 ![1152921504606847361, 302231454904756805305858, 77919046967349146032132, 9671406556917033397673992, 98320, 393248, 1298708368761643957013057709277248] ![(.leaf 0 (Common.fact 174).pointIds 174), (.leaf 1 (Common.fact 175).pointIds 175), (.leaf 2 (Common.fact 176).pointIds 176), (.leaf 3 (Common.fact 177).pointIds 177), (.leaf 4 (Common.fact 178).pointIds 178), B0386, (.leaf 6 (Common.fact 770).pointIds 770)]
theorem treeEq0385 : B0385.tree = HexagonCover.NBand.M6667_6700.SplitData.node0385 := by
  change Tree.branch (133 : Fin 173) _ = Tree.branch (133 : Fin 173) _
  apply congrArg (Tree.branch (133 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0386
  · rfl

def B0384 : Block := .branch 134 ![1152921504606847361, 302231454904756805305858, 77919046967349146032132, 9671406556917033397673992, 98320, 393248, 1298708368761643957013057709277248] ![(.leaf 0 (Common.fact 408).pointIds 408), (.leaf 1 (Common.fact 409).pointIds 409), (.leaf 2 (Common.fact 410).pointIds 410), (.leaf 3 (Common.fact 411).pointIds 411), (.leaf 4 (Common.fact 412).pointIds 412), B0385, (.leaf 6 (Common.fact 769).pointIds 769)]
theorem treeEq0384 : B0384.tree = HexagonCover.NBand.M6667_6700.SplitData.node0384 := by
  change Tree.branch (134 : Fin 173) _ = Tree.branch (134 : Fin 173) _
  apply congrArg (Tree.branch (134 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0385
  · rfl

theorem accepted0384 : B0384.accepted = true := by decide +kernel
theorem checked0384 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0384 (maskNeeds ![1152921504606847361, 302231454904756805305858, 77919046967349146032132, 9671406556917033397673992, 98320, 393248, 1298708368761643957013057709277248]) := by
  rw [← treeEq0384]
  exact B0384.sound accepted0384
#print axioms checked0384

def Tip0021_0023 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0023 ![1208926972536133781553537, 302231454904756805305858, 77919046967349146032132, 96714065569170333976518664, 98320, 393248, 1299025416811392811201899452170304] HexagonCover.NBand.M6667_6700.SplitTree.Run0004.checked0023
def B0375 : Block := .branch 167 ![1208926972536133781553537, 302231454904756805305858, 77919046967349146032132, 38685626227668133590622216, 2993155710065612352971116801974439986629133943799824, 1496577676626844588240573268701473812127674924400672, 7108743963977511794143356929003367177644021177122880] ![(.leaf 0 (Common.fact 714).pointIds 714), (.leaf 1 (Common.fact 736).pointIds 736), (.leaf 2 (Common.fact 262).pointIds 262), (.leaf 3 (Common.fact 755).pointIds 755), (.leaf 4 (Common.fact 737).pointIds 737), (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq0375 : B0375.tree = HexagonCover.NBand.M6667_6700.SplitData.node0375 := by
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

def B0374 : Block := .branch 170 ![1208926972536133781553537, 302231454904756805305858, 77919046967349146032132, 38685626227668133590622216, 2993155710239836924834637295267687785634199268065296, 393248, 7108743963977511794143356929003367177644021177122880] ![(.leaf 0 (Common.fact 732).pointIds 732), (.leaf 1 (Common.fact 733).pointIds 733), (.leaf 2 (Common.fact 497).pointIds 497), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 734).pointIds 734), B0375, (.leaf 6 (Common.fact 754).pointIds 754)]
theorem treeEq0374 : B0374.tree = HexagonCover.NBand.M6667_6700.SplitData.node0374 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0375
  · rfl

def B0373 : Block := .branch 169 ![1208926972536133781553537, 302231454904756805305858, 77919046967349146032132, 38685626227668133590622216, 2993155710239836924834637295267687785634199268065296, 21778071482940061661655974875633165926432, 6360455125664089500023070294652630271580183715119168] ![(.leaf 0 (Common.fact 728).pointIds 728), (.leaf 1 (Common.fact 729).pointIds 729), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 751).pointIds 751), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 752).pointIds 752), B0374]
theorem treeEq0373 : B0373.tree = HexagonCover.NBand.M6667_6700.SplitData.node0373 := by
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
  · exact treeEq0374

def B0372 : Block := .branch 171 ![1208926972536133781553537, 302231454904756805305858, 77919046967349146032132, 38685626227668133590622216, 356986147748353490757864740161378849420050448, 21778071482940061661655974875633165926432, 6360455125664089501321461421936394236063181973225536] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 725).pointIds 725), (.leaf 2 (Common.fact 499).pointIds 499), (.leaf 3 (Common.fact 749).pointIds 749), B0373, (.leaf 5 (Common.fact 541).pointIds 541), (.leaf 6 (Common.fact 750).pointIds 750)]
theorem treeEq0372 : B0372.tree = HexagonCover.NBand.M6667_6700.SplitData.node0372 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0373
  · rfl
  · rfl

def B0371 : Block := .branch 172 ![1208926972536133781553537, 302231454904756805305858, 77919046967349146032132, 38685626227668133590622216, 356986147748353490757864740161378849420050448, 21778071482940061661655974875633165926432, 374144419156711148359168347130498987552482277195840] ![(.leaf 0 (Common.fact 745).pointIds 745), (.leaf 1 (Common.fact 746).pointIds 746), (.leaf 2 (Common.fact 582).pointIds 582), (.leaf 3 (Common.fact 747).pointIds 747), (.leaf 4 (Common.fact 748).pointIds 748), (.leaf 5 (Common.fact 631).pointIds 631), B0372]
theorem treeEq0371 : B0371.tree = HexagonCover.NBand.M6667_6700.SplitData.node0371 := by
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
  · exact treeEq0372

def B0370 : Block := .branch 148 ![1208926972536133781553537, 302231454904756805305858, 77919046967349146032132, 38685626227668133590622216, 174224571863520493293247799005065324363792, 21778071482940061661655974875633165926432, 374144419156711148359168656615508808897551001976896] ![(.leaf 0 (Common.fact 390).pointIds 390), (.leaf 1 (Common.fact 391).pointIds 391), (.leaf 2 (Common.fact 392).pointIds 392), (.leaf 3 (Common.fact 393).pointIds 393), B0371, (.leaf 5 (Common.fact 394).pointIds 394), (.leaf 6 (Common.fact 744).pointIds 744)]
theorem treeEq0370 : B0370.tree = HexagonCover.NBand.M6667_6700.SplitData.node0370 := by
  change Tree.branch (148 : Fin 173) _ = Tree.branch (148 : Fin 173) _
  apply congrArg (Tree.branch (148 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0371
  · rfl
  · rfl

def B0369 : Block := .branch 168 ![1208926972536133781553537, 302231454904756805305858, 77919046967349146032132, 38685626227668133590622216, 174224571863520493293247799005065324363792, 21778071482940061661655974875633165926432, 1299025339440140355865632270975040] ![(.leaf 0 (Common.fact 713).pointIds 713), (.leaf 1 (Common.fact 719).pointIds 719), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 743).pointIds 743), (.leaf 4 (Common.fact 720).pointIds 720), (.leaf 5 (Common.fact 697).pointIds 697), B0370]
theorem treeEq0369 : B0369.tree = HexagonCover.NBand.M6667_6700.SplitData.node0369 := by
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
  · exact treeEq0370

def B0368 : Block := .branch 134 ![1208926972536133781553537, 302231454904756805305858, 77919046967349146032132, 38685626227668133590622216, 174224571863520493293247799005065324363792, 393248, 1299025339440140355865632270975040] ![(.leaf 0 (Common.fact 408).pointIds 408), (.leaf 1 (Common.fact 409).pointIds 409), (.leaf 2 (Common.fact 410).pointIds 410), (.leaf 3 (Common.fact 411).pointIds 411), (.leaf 4 (Common.fact 412).pointIds 412), B0369, (.leaf 6 (Common.fact 742).pointIds 742)]
theorem treeEq0368 : B0368.tree = HexagonCover.NBand.M6667_6700.SplitData.node0368 := by
  change Tree.branch (134 : Fin 173) _ = Tree.branch (134 : Fin 173) _
  apply congrArg (Tree.branch (134 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0369
  · rfl

def B0367 : Block := .branch 137 ![1208926972536133781553537, 302231454904756805305858, 77919046967349146032132, 58028439341502200385921032, 98320, 393248, 1299025339440140355865632270975040] ![(.leaf 0 (Common.fact 402).pointIds 402), (.leaf 1 (Common.fact 403).pointIds 403), (.leaf 2 (Common.fact 404).pointIds 404), (.leaf 3 (Common.fact 405).pointIds 405), B0368, (.leaf 5 (Common.fact 406).pointIds 406), (.leaf 6 (Common.fact 741).pointIds 741)]
theorem treeEq0367 : B0367.tree = HexagonCover.NBand.M6667_6700.SplitData.node0367 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0368
  · rfl
  · rfl

def B0366 : Block := .branch 143 ![1208926972536133781553537, 302231454904756805305858, 77919046967349146032132, 58028439341502200385921032, 98320, 393248, 1299025339440140355865632270975040] ![(.leaf 0 (Common.fact 396).pointIds 396), (.leaf 1 (Common.fact 397).pointIds 397), (.leaf 2 (Common.fact 398).pointIds 398), (.leaf 3 (Common.fact 399).pointIds 399), (.leaf 4 (Common.fact 400).pointIds 400), B0367, (.leaf 6 (Common.fact 740).pointIds 740)]
theorem treeEq0366 : B0366.tree = HexagonCover.NBand.M6667_6700.SplitData.node0366 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0367
  · rfl

def B0022 : Block := .branch 86 ![1208926972536133781553537, 302231454904756805305858, 77919046967349146032132, 58028439341502200385921032, 98320, 393248, 1299025416811392811201899452170304] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), Tip0021_0023, (.leaf 4 (Common.fact 115).pointIds 115), (.leaf 5 (Common.fact 116).pointIds 116), B0366]
theorem treeEq0022 : B0022.tree = HexagonCover.NBand.M6667_6700.SplitData.node0022 := by
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
  · exact treeEq0366

def B0382 : Block := .branch 129 ![385, 1538, 6148, 24584, 187072209752580145393592151880932025521024689864720, 393248, 2993155353253689177779854925507404695102474352590912] ![(.leaf 0 (Common.fact 555).pointIds 555), (.leaf 1 (Common.fact 556).pointIds 556), (.leaf 2 (Common.fact 557).pointIds 557), (.leaf 3 (Common.fact 558).pointIds 558), (.leaf 4 (Common.fact 766).pointIds 766), (.leaf 5 (Common.fact 559).pointIds 559), (.leaf 6 (Common.fact 767).pointIds 767)]
theorem treeEq0382 : B0382.tree = HexagonCover.NBand.M6667_6700.SplitData.node0382 := by
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
  · rfl

def B0381 : Block := .branch 171 ![1208926972536133781553537, 302231454904756805305858, 77919046967349146032132, 19342813113834066795323400, 187072209752580145393592151880932025521024689864720, 10889035741470030830827987437816583159840, 1298708388104457070847124504576064] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 725).pointIds 725), (.leaf 2 (Common.fact 499).pointIds 499), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 765).pointIds 765), B0382]
theorem treeEq0381 : B0381.tree = HexagonCover.NBand.M6667_6700.SplitData.node0381 := by
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
  · exact treeEq0382

def B0380 : Block := .branch 167 ![1208926972536133781553537, 302231454904756805305858, 77919046967349146032132, 19342813113834066795323400, 174224571863520493293247799005065324363792, 10889035741470030830827987437816583159840, 1298708388104457070847124504576064] ![(.leaf 0 (Common.fact 714).pointIds 714), (.leaf 1 (Common.fact 736).pointIds 736), (.leaf 2 (Common.fact 262).pointIds 262), (.leaf 3 (Common.fact 761).pointIds 761), B0381, (.leaf 5 (Common.fact 361).pointIds 361), (.leaf 6 (Common.fact 762).pointIds 762)]
theorem treeEq0380 : B0380.tree = HexagonCover.NBand.M6667_6700.SplitData.node0380 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0381
  · rfl
  · rfl

def B0379 : Block := .branch 133 ![1208926972536133781553537, 302231454904756805305858, 77919046967349146032132, 19342813113834066795323400, 174224571863520493293247799005065324363792, 393248, 1298708388104457070847124504576064] ![(.leaf 0 (Common.fact 174).pointIds 174), (.leaf 1 (Common.fact 175).pointIds 175), (.leaf 2 (Common.fact 176).pointIds 176), (.leaf 3 (Common.fact 177).pointIds 177), (.leaf 4 (Common.fact 178).pointIds 178), B0380, (.leaf 6 (Common.fact 760).pointIds 760)]
theorem treeEq0379 : B0379.tree = HexagonCover.NBand.M6667_6700.SplitData.node0379 := by
  change Tree.branch (133 : Fin 173) _ = Tree.branch (133 : Fin 173) _
  apply congrArg (Tree.branch (133 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0380
  · rfl

def B0378 : Block := .branch 134 ![1208926972536133781553537, 302231454904756805305858, 77919046967349146032132, 19342813113834066795323400, 174224571863520493293247799005065324363792, 393248, 1298708388104457070847124504576064] ![(.leaf 0 (Common.fact 408).pointIds 408), (.leaf 1 (Common.fact 409).pointIds 409), (.leaf 2 (Common.fact 410).pointIds 410), (.leaf 3 (Common.fact 411).pointIds 411), (.leaf 4 (Common.fact 412).pointIds 412), B0379, (.leaf 6 (Common.fact 759).pointIds 759)]
theorem treeEq0378 : B0378.tree = HexagonCover.NBand.M6667_6700.SplitData.node0378 := by
  change Tree.branch (134 : Fin 173) _ = Tree.branch (134 : Fin 173) _
  apply congrArg (Tree.branch (134 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0379
  · rfl

def B0377 : Block := .branch 137 ![1208926972536133781553537, 302231454904756805305858, 77919046967349146032132, 19342813113834066795323400, 98320, 393248, 1298708388104457070847124504576064] ![(.leaf 0 (Common.fact 402).pointIds 402), (.leaf 1 (Common.fact 403).pointIds 403), (.leaf 2 (Common.fact 404).pointIds 404), (.leaf 3 (Common.fact 405).pointIds 405), B0378, (.leaf 5 (Common.fact 406).pointIds 406), (.leaf 6 (Common.fact 758).pointIds 758)]
theorem treeEq0377 : B0377.tree = HexagonCover.NBand.M6667_6700.SplitData.node0377 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0378
  · rfl
  · rfl

def B0376 : Block := .branch 143 ![1208926972536133781553537, 302231454904756805305858, 77919046967349146032132, 19342813113834066795323400, 98320, 393248, 1298708388104457070847124504576064] ![(.leaf 0 (Common.fact 396).pointIds 396), (.leaf 1 (Common.fact 397).pointIds 397), (.leaf 2 (Common.fact 398).pointIds 398), (.leaf 3 (Common.fact 399).pointIds 399), (.leaf 4 (Common.fact 400).pointIds 400), B0377, (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq0376 : B0376.tree = HexagonCover.NBand.M6667_6700.SplitData.node0376 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0377
  · rfl

def B0021 : Block := .branch 85 ![1208926972536133781553537, 302231454904756805305858, 77919046967349146032132, 19342813113834066795323400, 98320, 393248, 1299025416811392811201899452170304] ![(.leaf 0 (Common.fact 107).pointIds 107), (.leaf 1 (Common.fact 108).pointIds 108), (.leaf 2 (Common.fact 109).pointIds 109), B0022, (.leaf 4 (Common.fact 110).pointIds 110), (.leaf 5 (Common.fact 111).pointIds 111), B0376]
theorem treeEq0021 : B0021.tree = HexagonCover.NBand.M6667_6700.SplitData.node0021 := by
  change Tree.branch (85 : Fin 173) _ = Tree.branch (85 : Fin 173) _
  apply congrArg (Tree.branch (85 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0022
  · rfl
  · rfl
  · exact treeEq0376

theorem accepted0021 : B0021.accepted = true := by decide +kernel
theorem checked0021 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0021 (maskNeeds ![1208926972536133781553537, 302231454904756805305858, 77919046967349146032132, 19342813113834066795323400, 98320, 393248, 1299025416811392811201899452170304]) := by
  rw [← treeEq0021]
  exact B0021.sound accepted0021
#print axioms checked0021

def B0424 : Block := .branch 167 ![4951760158294442604203344257, 302231454904756805305858, 77919046967349146032132, 87112285931918741657278655845853340655624, 5846720173169964977273822132276583609347942219792, 1432833768041334006874500727005095043342401568, 2787593149816644961293452571719132656435264] ![(.leaf 0 (Common.fact 839).pointIds 839), (.leaf 1 (Common.fact 736).pointIds 736), (.leaf 2 (Common.fact 262).pointIds 262), (.leaf 3 (Common.fact 840).pointIds 840), (.leaf 4 (Common.fact 841).pointIds 841), (.leaf 5 (Common.fact 249).pointIds 249), (.leaf 6 (Common.fact 842).pointIds 842)]
theorem treeEq0424 : B0424.tree = HexagonCover.NBand.M6667_6700.SplitData.node0424 := by
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

def B0423 : Block := .branch 85 ![4951760158294442604203344257, 302231454904756805305858, 77919046967349146032132, 87112285931918702971652428177719750057992, 5846720173169964977273822132276583609347942219792, 1432833768041334006874500727005095043342401568, 2787593151114719175927159478851756738740288] ![(.leaf 0 (Common.fact 107).pointIds 107), (.leaf 1 (Common.fact 108).pointIds 108), (.leaf 2 (Common.fact 109).pointIds 109), B0424, (.leaf 4 (Common.fact 110).pointIds 110), (.leaf 5 (Common.fact 111).pointIds 111), (.leaf 6 (Common.fact 838).pointIds 838)]
theorem treeEq0423 : B0423.tree = HexagonCover.NBand.M6667_6700.SplitData.node0423 := by
  change Tree.branch (85 : Fin 173) _ = Tree.branch (85 : Fin 173) _
  apply congrArg (Tree.branch (85 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0424
  · rfl
  · rfl
  · rfl

def B0422 : Block := .branch 92 ![1152921504606847361, 302231454904756805305858, 77919046967349146032132, 87112285931918702971652428177719750057992, 5846720173169964977273822132276583609347942219792, 1432833768041334006874500727005095043342401568, 2787593151114719175927159478851756738740288] ![B0423, (.leaf 1 (Common.fact 832).pointIds 832), (.leaf 2 (Common.fact 833).pointIds 833), (.leaf 3 (Common.fact 834).pointIds 834), (.leaf 4 (Common.fact 835).pointIds 835), (.leaf 5 (Common.fact 836).pointIds 836), (.leaf 6 (Common.fact 837).pointIds 837)]
theorem treeEq0422 : B0422.tree = HexagonCover.NBand.M6667_6700.SplitData.node0422 := by
  change Tree.branch (92 : Fin 173) _ = Tree.branch (92 : Fin 173) _
  apply congrArg (Tree.branch (92 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0423
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0421 : Block := .branch 108 ![1152921504606847361, 302231454904756805305858, 77919046967349146032132, 87112285931918702971652428177719750057992, 5846720173169964652755268473849856826191921643536, 1432833768041334006874500727005095043342401568, 2787593151114719175927159478851756738740288] ![(.leaf 0 (Common.fact 132).pointIds 132), (.leaf 1 (Common.fact 133).pointIds 133), (.leaf 2 (Common.fact 134).pointIds 134), (.leaf 3 (Common.fact 135).pointIds 135), B0422, (.leaf 5 (Common.fact 136).pointIds 136), (.leaf 6 (Common.fact 831).pointIds 831)]
theorem treeEq0421 : B0421.tree = HexagonCover.NBand.M6667_6700.SplitData.node0421 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0422
  · rfl
  · rfl

def B0420 : Block := .branch 119 ![1152921504606847361, 302231454904756805305858, 77919046967349146032132, 87112285931918702971652428177719750057992, 5846720173169964652755268473849856826191921643536, 1432833768041334006874500727005095043342401568, 2787593151114719175927159478851756738740288] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), B0421, (.leaf 5 (Common.fact 419).pointIds 419), (.leaf 6 (Common.fact 830).pointIds 830)]
theorem treeEq0420 : B0420.tree = HexagonCover.NBand.M6667_6700.SplitData.node0420 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0421
  · rfl
  · rfl

def B0419 : Block := .branch 97 ![1152921504606847361, 302231454904756805305858, 77919046967349146032132, 87112285931760246646623899502532662157320, 5846720173169964652755268473849856826191921643536, 1432833768041334006874500727005095043342401568, 2787593151114719175927159478851756738740288] ![(.leaf 0 (Common.fact 462).pointIds 462), (.leaf 1 (Common.fact 463).pointIds 463), (.leaf 2 (Common.fact 464).pointIds 464), B0420, (.leaf 4 (Common.fact 828).pointIds 828), (.leaf 5 (Common.fact 466).pointIds 466), (.leaf 6 (Common.fact 829).pointIds 829)]
theorem treeEq0419 : B0419.tree = HexagonCover.NBand.M6667_6700.SplitData.node0419 := by
  change Tree.branch (97 : Fin 173) _ = Tree.branch (97 : Fin 173) _
  apply congrArg (Tree.branch (97 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0420
  · rfl
  · rfl
  · rfl

def B0418 : Block := .branch 128 ![1152921504606847361, 302231454904756805305858, 77919046967349146032132, 87112286094019523475837262894110672445448, 5846720173169964652755268473849856826191921643536, 1432833768041334006874500727005095043342401568, 2787593151114719175927159478851756738740288] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 826).pointIds 826), B0419, (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 827).pointIds 827)]
theorem treeEq0418 : B0418.tree = HexagonCover.NBand.M6667_6700.SplitData.node0418 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0419
  · rfl
  · rfl

def B0417 : Block := .branch 107 ![1152921504606847361, 302231454904756805305858, 77919046967349146032132, 87112285931760246646623899502532662157320, 5846720173169964652755268473849856826191921643536, 1432833768041334006874500727005095043342401568, 2787593151114719175927159478851756738740288] ![(.leaf 0 (Common.fact 467).pointIds 467), (.leaf 1 (Common.fact 468).pointIds 468), (.leaf 2 (Common.fact 469).pointIds 469), B0418, (.leaf 4 (Common.fact 824).pointIds 824), (.leaf 5 (Common.fact 471).pointIds 471), (.leaf 6 (Common.fact 825).pointIds 825)]
theorem treeEq0417 : B0417.tree = HexagonCover.NBand.M6667_6700.SplitData.node0417 := by
  change Tree.branch (107 : Fin 173) _ = Tree.branch (107 : Fin 173) _
  apply congrArg (Tree.branch (107 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0418
  · rfl
  · rfl
  · rfl

def B0416 : Block := .branch 118 ![1152921504606847361, 302231454904756805305858, 77919046967349146032132, 87112285931760246646623899502532662157320, 5846720173169964652755268473849856826191921643536, 1432833768041334006874500727005095043342401568, 2787593151114719175927159478851756738740288] ![(.leaf 0 (Common.fact 472).pointIds 472), (.leaf 1 (Common.fact 473).pointIds 473), (.leaf 2 (Common.fact 474).pointIds 474), B0417, (.leaf 4 (Common.fact 822).pointIds 822), (.leaf 5 (Common.fact 476).pointIds 476), (.leaf 6 (Common.fact 823).pointIds 823)]
theorem treeEq0416 : B0416.tree = HexagonCover.NBand.M6667_6700.SplitData.node0416 := by
  change Tree.branch (118 : Fin 173) _ = Tree.branch (118 : Fin 173) _
  apply congrArg (Tree.branch (118 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0417
  · rfl
  · rfl
  · rfl

def B0415 : Block := .branch 141 ![1152921504606847361, 302231454904756805305858, 77919046967349146032132, 87112285931760246646623899502532662157320, 5846720173169964652755268473849856826191921643536, 1432833768041334006874500727005095043342401568, 1298391283235194694770711550492736] ![(.leaf 0 (Common.fact 179).pointIds 179), (.leaf 1 (Common.fact 180).pointIds 180), (.leaf 2 (Common.fact 181).pointIds 181), (.leaf 3 (Common.fact 182).pointIds 182), (.leaf 4 (Common.fact 774).pointIds 774), (.leaf 5 (Common.fact 821).pointIds 821), B0416]
theorem treeEq0415 : B0415.tree = HexagonCover.NBand.M6667_6700.SplitData.node0415 := by
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
  · exact treeEq0416

def B0414 : Block := .branch 127 ![1152921504606847361, 302231454904756805305858, 77919046967349146032132, 87112285931760246646623899502532662157320, 5846720173169964652755268473849856826191921643536, 1432833768041334006874500727005095043342401568, 1298391283235194694770711550492736] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), B0415, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 481).pointIds 481), (.leaf 6 (Common.fact 820).pointIds 820)]
theorem treeEq0414 : B0414.tree = HexagonCover.NBand.M6667_6700.SplitData.node0414 := by
  change Tree.branch (127 : Fin 173) _ = Tree.branch (127 : Fin 173) _
  apply congrArg (Tree.branch (127 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0415
  · rfl
  · rfl
  · rfl

def B0413 : Block := .branch 136 ![1152921504606847361, 302231454904756805305858, 77919046967349146032132, 24584, 5846720173169964652755268473849856826191921643536, 1432833768041334006874500727005095043342401568, 1298391283235194694770711550492736] ![(.leaf 0 (Common.fact 190).pointIds 190), (.leaf 1 (Common.fact 191).pointIds 191), (.leaf 2 (Common.fact 192).pointIds 192), B0414, (.leaf 4 (Common.fact 818).pointIds 818), (.leaf 5 (Common.fact 193).pointIds 193), (.leaf 0 [] 0)]
theorem treeEq0413 : B0413.tree = HexagonCover.NBand.M6667_6700.SplitData.node0413 := by
  change Tree.branch (136 : Fin 173) _ = Tree.branch (136 : Fin 173) _
  apply congrArg (Tree.branch (136 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0414
  · rfl
  · rfl
  · rfl

def B0412 : Block := .branch 149 ![1152921504606847361, 302231454904756805305858, 77919046967349146032132, 24584, 5846006549323611672814739330865132078623730270224, 1432833768041334006874500727005095043342401568, 1298391283235194694770711550492736] ![(.leaf 0 (Common.fact 204).pointIds 204), (.leaf 1 (Common.fact 205).pointIds 205), (.leaf 2 (Common.fact 206).pointIds 206), (.leaf 3 (Common.fact 207).pointIds 207), B0413, (.leaf 5 (Common.fact 816).pointIds 816), (.leaf 6 (Common.fact 817).pointIds 817)]
theorem treeEq0412 : B0412.tree = HexagonCover.NBand.M6667_6700.SplitData.node0412 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0413
  · rfl
  · rfl

def B0411 : Block := .branch 133 ![1152921504606847361, 302231454904756805305858, 77919046967349146032132, 24584, 5846006549323611672814739330865132078623730270224, 1432822879005592536843669899017657226759634976, 8166778104493806358315685349073987567680] ![(.leaf 0 (Common.fact 174).pointIds 174), (.leaf 1 (Common.fact 175).pointIds 175), (.leaf 2 (Common.fact 176).pointIds 176), (.leaf 3 (Common.fact 177).pointIds 177), (.leaf 4 (Common.fact 178).pointIds 178), B0412, (.leaf 6 (Common.fact 815).pointIds 815)]
theorem treeEq0411 : B0411.tree = HexagonCover.NBand.M6667_6700.SplitData.node0411 := by
  change Tree.branch (133 : Fin 173) _ = Tree.branch (133 : Fin 173) _
  apply congrArg (Tree.branch (133 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0412
  · rfl

def B0410 : Block := .branch 142 ![1152921504606847361, 302231454904756805305858, 77919046967349146032132, 24584, 5846006549323611672814739330865132078623730270224, 1427247692705959881058285969449495136383139872, 8166778104493806358315685349073987567680] ![(.leaf 0 (Common.fact 199).pointIds 199), (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 813).pointIds 813), B0411, (.leaf 6 (Common.fact 814).pointIds 814)]
theorem treeEq0410 : B0410.tree = HexagonCover.NBand.M6667_6700.SplitData.node0410 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0411
  · rfl

def B0409 : Block := .branch 131 ![1152921504606847361, 302231454904756805305858, 77919046967349146032132, 24584, 5846006549323611672814739330865132078623730270224, 1427247692705959881058285969449495136383139872, 5444519169126298650608688489619841876032] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 812).pointIds 812), (.leaf 5 (Common.fact 148).pointIds 148), B0410]
theorem treeEq0409 : B0409.tree = HexagonCover.NBand.M6667_6700.SplitData.node0409 := by
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
  · exact treeEq0410

def B0408 : Block := .branch 132 ![1152921504606847361, 302231454904756805305858, 77919046967349146032132, 24584, 5846006549323611672814739330865132078623730270224, 1427247692705959881058285969449495136383139872, 1298391283235194694770711550492736] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 811).pointIds 811), (.leaf 5 (Common.fact 142).pointIds 142), B0409]
theorem treeEq0408 : B0408.tree = HexagonCover.NBand.M6667_6700.SplitData.node0408 := by
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
  · exact treeEq0409

def B0407 : Block := .branch 150 ![1152921504606847361, 302231454904756805305858, 77919046967349146032132, 24584, 5846006549323611672814739330865132078623730270224, 393248, 1298391283235194694770711550492736] ![(.leaf 0 (Common.fact 209).pointIds 209), (.leaf 1 (Common.fact 210).pointIds 210), (.leaf 2 (Common.fact 211).pointIds 211), (.leaf 3 (Common.fact 212).pointIds 212), (.leaf 4 (Common.fact 809).pointIds 809), B0408, (.leaf 6 (Common.fact 810).pointIds 810)]
theorem treeEq0407 : B0407.tree = HexagonCover.NBand.M6667_6700.SplitData.node0407 := by
  change Tree.branch (150 : Fin 173) _ = Tree.branch (150 : Fin 173) _
  apply congrArg (Tree.branch (150 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0408
  · rfl

def B0406 : Block := .branch 162 ![1152921504606847361, 302231454904756805305858, 77919046967349146032132, 24584, 98320, 393248, 1298391283235194694770711550492736] ![(.leaf 0 (Common.fact 223).pointIds 223), (.leaf 1 (Common.fact 224).pointIds 224), (.leaf 2 (Common.fact 225).pointIds 225), (.leaf 3 (Common.fact 226).pointIds 226), B0407, (.leaf 5 (Common.fact 227).pointIds 227), (.leaf 6 (Common.fact 808).pointIds 808)]
theorem treeEq0406 : B0406.tree = HexagonCover.NBand.M6667_6700.SplitData.node0406 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0407
  · rfl
  · rfl

theorem accepted0406 : B0406.accepted = true := by decide +kernel
theorem checked0406 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0406 (maskNeeds ![1152921504606847361, 302231454904756805305858, 77919046967349146032132, 24584, 98320, 393248, 1298391283235194694770711550492736]) := by
  rw [← treeEq0406]
  exact B0406.sound accepted0406
#print axioms checked0406

def B0437 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 1122433257470133441180746864478393871350337417773120] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 871).pointIds 871)]
theorem treeEq0437 : B0437.tree = HexagonCover.NBand.M6667_6700.SplitData.node0437 := by
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

def B0436 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 77919046967349146032132, 39623752663689085830169649160, 2993155710065612352971116801974439986629133943799824, 11150372599265311570767859136324180753383456, 374144419156711147060460230127656965286499955769408] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 869).pointIds 869), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 731).pointIds 731), B0437]
theorem treeEq0436 : B0436.tree = HexagonCover.NBand.M6667_6700.SplitData.node0436 := by
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
  · exact treeEq0437

def B0435 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 77919046967349146032132, 39643095476802919896964947976, 356811923176489970264571492362373784095784976, 11150372599265311570767859136324180753383456, 374144419156711148358534599503868783091658400464960] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 499).pointIds 499), (.leaf 3 (Common.fact 763).pointIds 763), B0436, (.leaf 5 (Common.fact 726).pointIds 726), (.leaf 6 (Common.fact 866).pointIds 866)]
theorem treeEq0435 : B0435.tree = HexagonCover.NBand.M6667_6700.SplitData.node0435 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0436
  · rfl
  · rfl

def B0440 : Block := .branch 132 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 374144419156711148358217551454119928902816657571904] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 802).pointIds 802), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 880).pointIds 880)]
theorem treeEq0440 : B0440.tree = HexagonCover.NBand.M6667_6700.SplitData.node0440 := by
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

def B0439 : Block := .branch 167 ![4951760158294442604203344257, 147573953689188042242, 77919046967349146032132, 39623752663689085830169649160, 98320, 1496577676626844588240573268701473812127674924400672, 374144419156711148358217551454119928902816657571904] ![(.leaf 0 (Common.fact 839).pointIds 839), (.leaf 1 (Common.fact 877).pointIds 877), (.leaf 2 (Common.fact 262).pointIds 262), (.leaf 3 (Common.fact 878).pointIds 878), B0440, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 879).pointIds 879)]
theorem treeEq0439 : B0439.tree = HexagonCover.NBand.M6667_6700.SplitData.node0439 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0440
  · rfl
  · rfl

def B0438 : Block := .branch 170 ![4951760158294442604203344257, 147573953689188042242, 77919046967349146032132, 39623752663689085830169649160, 356811923176489970264571492362373784095784976, 393248, 374144419156711148358217551454119928902816657571904] ![(.leaf 0 (Common.fact 872).pointIds 872), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 497).pointIds 497), (.leaf 3 (Common.fact 874).pointIds 874), (.leaf 4 (Common.fact 875).pointIds 875), B0439, (.leaf 6 (Common.fact 876).pointIds 876)]
theorem treeEq0438 : B0438.tree = HexagonCover.NBand.M6667_6700.SplitData.node0438 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0439
  · rfl

def B0434 : Block := .branch 84 ![4951760158294442604203344257, 147573953689188042242, 77937493711422855583748, 39623752663689085830169649160, 356811923176489970264571492362373784095784976, 11150372599265311570767859136324180753383456, 374144419156711148358534599503868783091658400464960] ![(.leaf 0 (Common.fact 102).pointIds 102), (.leaf 1 (Common.fact 103).pointIds 103), (.leaf 2 (Common.fact 104).pointIds 104), B0435, (.leaf 4 (Common.fact 105).pointIds 105), (.leaf 5 (Common.fact 106).pointIds 106), B0438]
theorem treeEq0434 : B0434.tree = HexagonCover.NBand.M6667_6700.SplitData.node0434 := by
  change Tree.branch (84 : Fin 173) _ = Tree.branch (84 : Fin 173) _
  apply congrArg (Tree.branch (84 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0435
  · rfl
  · rfl
  · exact treeEq0438

def B0443 : Block := .branch 108 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 374144419156711148358534445970289692033753212780608] ![(.leaf 0 (Common.fact 132).pointIds 132), (.leaf 1 (Common.fact 133).pointIds 133), (.leaf 2 (Common.fact 134).pointIds 134), (.leaf 3 (Common.fact 135).pointIds 135), (.leaf 4 (Common.fact 374).pointIds 374), (.leaf 5 (Common.fact 136).pointIds 136), (.leaf 6 (Common.fact 883).pointIds 883)]
theorem treeEq0443 : B0443.tree = HexagonCover.NBand.M6667_6700.SplitData.node0443 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0442 : Block := .branch 167 ![4951760158294442604203344257, 147573953689188042242, 77919046967349146032132, 39623752663689085830169649160, 98320, 1496577676626844588240573268701473812127674924400672, 374144419156711148358534445970289692033753212780608] ![(.leaf 0 (Common.fact 839).pointIds 839), (.leaf 1 (Common.fact 877).pointIds 877), (.leaf 2 (Common.fact 262).pointIds 262), (.leaf 3 (Common.fact 878).pointIds 878), B0443, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 882).pointIds 882)]
theorem treeEq0442 : B0442.tree = HexagonCover.NBand.M6667_6700.SplitData.node0442 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0443
  · rfl
  · rfl

def B0441 : Block := .branch 170 ![4951760158294442604203344257, 147573953689188042242, 77919046967349146032132, 39623752663689085830169649160, 356811923176489970264571492362373784095784976, 393248, 374144419156711148358534445970289692033753212780608] ![(.leaf 0 (Common.fact 872).pointIds 872), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 497).pointIds 497), (.leaf 3 (Common.fact 874).pointIds 874), (.leaf 4 (Common.fact 875).pointIds 875), B0442, (.leaf 6 (Common.fact 881).pointIds 881)]
theorem treeEq0441 : B0441.tree = HexagonCover.NBand.M6667_6700.SplitData.node0441 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0442
  · rfl

def B0433 : Block := .branch 80 ![4951760158294442604203344257, 147573953689188042242, 77937493711422855583748, 39623752663689085830169649160, 356811923176489970264571492362373784095784976, 11150372599265311570767859136324180753383456, 374144419156711148358534599503868783091658400464960] ![B0434, (.leaf 1 (Common.fact 92).pointIds 92), (.leaf 2 (Common.fact 93).pointIds 93), (.leaf 3 (Common.fact 94).pointIds 94), (.leaf 4 (Common.fact 95).pointIds 95), (.leaf 5 (Common.fact 96).pointIds 96), B0441]
theorem treeEq0433 : B0433.tree = HexagonCover.NBand.M6667_6700.SplitData.node0433 := by
  change Tree.branch (80 : Fin 173) _ = Tree.branch (80 : Fin 173) _
  apply congrArg (Tree.branch (80 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0434
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0441

def B0432 : Block := .branch 134 ![4951760158294442604203344257, 147573953689188042242, 77937493711422855583748, 39623752663689085830169649160, 356811923176489970264571492362373784095784976, 11150372599265311570767859136324180753383456, 374144419156711148358534599503868783091658400464960] ![(.leaf 0 (Common.fact 408).pointIds 408), (.leaf 1 (Common.fact 409).pointIds 409), (.leaf 2 (Common.fact 410).pointIds 410), (.leaf 3 (Common.fact 411).pointIds 411), (.leaf 4 (Common.fact 412).pointIds 412), B0433, (.leaf 6 (Common.fact 863).pointIds 863)]
theorem treeEq0432 : B0432.tree = HexagonCover.NBand.M6667_6700.SplitData.node0432 := by
  change Tree.branch (134 : Fin 173) _ = Tree.branch (134 : Fin 173) _
  apply congrArg (Tree.branch (134 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0433
  · rfl

def B0431 : Block := .branch 168 ![4951760158294442604203344257, 147573953689188042242, 77937493711422855583748, 39623752663689085830169649160, 356811923176489970264571492362373784095784976, 11150372599265311570767859136324180753383456, 1298391282328500330059739669463104] ![(.leaf 0 (Common.fact 859).pointIds 859), (.leaf 1 (Common.fact 860).pointIds 860), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 861).pointIds 861), (.leaf 4 (Common.fact 862).pointIds 862), (.leaf 5 (Common.fact 721).pointIds 721), B0432]
theorem treeEq0431 : B0431.tree = HexagonCover.NBand.M6667_6700.SplitData.node0431 := by
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
  · exact treeEq0432

def B0430 : Block := .branch 83 ![4951760158294442604203344257, 147573953689188042242, 77937493711422855583748, 39614081257132168796771999752, 356811923176489970264571492362373784095784976, 11150372599265311570767859136324180753383456, 1298391282328500330059739669463104] ![(.leaf 0 (Common.fact 97).pointIds 97), (.leaf 1 (Common.fact 98).pointIds 98), (.leaf 2 (Common.fact 99).pointIds 99), B0431, (.leaf 4 (Common.fact 100).pointIds 100), (.leaf 5 (Common.fact 101).pointIds 101), (.leaf 6 (Common.fact 858).pointIds 858)]
theorem treeEq0430 : B0430.tree = HexagonCover.NBand.M6667_6700.SplitData.node0430 := by
  change Tree.branch (83 : Fin 173) _ = Tree.branch (83 : Fin 173) _
  apply congrArg (Tree.branch (83 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0431
  · rfl
  · rfl
  · rfl

def B0429 : Block := .branch 92 ![1152921504606847361, 147573953689188042242, 77937493711422855583748, 39614081257132168796771999752, 356811923176489970264571492362373784095784976, 11150372599265311570767859136324180753383456, 1298391282328500330059739669463104] ![B0430, (.leaf 1 (Common.fact 832).pointIds 832), (.leaf 2 (Common.fact 833).pointIds 833), (.leaf 3 (Common.fact 834).pointIds 834), (.leaf 4 (Common.fact 835).pointIds 835), (.leaf 5 (Common.fact 836).pointIds 836), (.leaf 6 (Common.fact 857).pointIds 857)]
theorem treeEq0429 : B0429.tree = HexagonCover.NBand.M6667_6700.SplitData.node0429 := by
  change Tree.branch (92 : Fin 173) _ = Tree.branch (92 : Fin 173) _
  apply congrArg (Tree.branch (92 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0430
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0428 : Block := .branch 95 ![1152921504606847361, 147573953689188042242, 77937493711422855583748, 24584, 356811923176489970264571492362373784095784976, 11150372599265311570767859136324180753383456, 1298391282328500330059739669463104] ![(.leaf 0 (Common.fact 851).pointIds 851), (.leaf 1 (Common.fact 852).pointIds 852), (.leaf 2 (Common.fact 853).pointIds 853), B0429, (.leaf 4 (Common.fact 854).pointIds 854), (.leaf 5 (Common.fact 855).pointIds 855), (.leaf 6 (Common.fact 856).pointIds 856)]
theorem treeEq0428 : B0428.tree = HexagonCover.NBand.M6667_6700.SplitData.node0428 := by
  change Tree.branch (95 : Fin 173) _ = Tree.branch (95 : Fin 173) _
  apply congrArg (Tree.branch (95 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0429
  · rfl
  · rfl
  · rfl

def B0427 : Block := .branch 105 ![1152921504606847361, 147573953689188042242, 77937493711422855583748, 24584, 356811923176489970264571492362373784095784976, 11150372599265311570767859136324180753383456, 1298391282328500330059739669463104] ![(.leaf 0 (Common.fact 845).pointIds 845), (.leaf 1 (Common.fact 846).pointIds 846), (.leaf 2 (Common.fact 847).pointIds 847), B0428, (.leaf 4 (Common.fact 848).pointIds 848), (.leaf 5 (Common.fact 849).pointIds 849), (.leaf 6 (Common.fact 850).pointIds 850)]
theorem treeEq0427 : B0427.tree = HexagonCover.NBand.M6667_6700.SplitData.node0427 := by
  change Tree.branch (105 : Fin 173) _ = Tree.branch (105 : Fin 173) _
  apply congrArg (Tree.branch (105 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0428
  · rfl
  · rfl
  · rfl

def B0426 : Block := .branch 143 ![1152921504606847361, 147573953689188042242, 77937493711422855583748, 24584, 356811923176489970264571492362373784095784976, 393248, 1298391282328500330059739669463104] ![(.leaf 0 (Common.fact 396).pointIds 396), (.leaf 1 (Common.fact 397).pointIds 397), (.leaf 2 (Common.fact 398).pointIds 398), (.leaf 3 (Common.fact 399).pointIds 399), (.leaf 4 (Common.fact 400).pointIds 400), B0427, (.leaf 6 (Common.fact 844).pointIds 844)]
theorem treeEq0426 : B0426.tree = HexagonCover.NBand.M6667_6700.SplitData.node0426 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0427
  · rfl

def B0425 : Block := .branch 148 ![1152921504606847361, 147573953689188042242, 77937493711422855583748, 24584, 98320, 393248, 1298391282328500330059739669463104] ![(.leaf 0 (Common.fact 390).pointIds 390), (.leaf 1 (Common.fact 391).pointIds 391), (.leaf 2 (Common.fact 392).pointIds 392), (.leaf 3 (Common.fact 393).pointIds 393), B0426, (.leaf 5 (Common.fact 394).pointIds 394), (.leaf 6 (Common.fact 843).pointIds 843)]
theorem treeEq0425 : B0425.tree = HexagonCover.NBand.M6667_6700.SplitData.node0425 := by
  change Tree.branch (148 : Fin 173) _ = Tree.branch (148 : Fin 173) _
  apply congrArg (Tree.branch (148 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0426
  · rfl
  · rfl

theorem accepted0425 : B0425.accepted = true := by decide +kernel
theorem checked0425 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0425 (maskNeeds ![1152921504606847361, 147573953689188042242, 77937493711422855583748, 24584, 98320, 393248, 1298391282328500330059739669463104]) := by
  rw [← treeEq0425]
  exact B0425.sound accepted0425
#print axioms checked0425

end HexagonCover.NBand.M6667_6700.SplitTree.Run0005
