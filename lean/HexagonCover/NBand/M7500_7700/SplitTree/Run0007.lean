import HexagonCover.NBand.M7500_7700.SplitData
import HexagonCover.NBand.M7500_7700.SplitTree.Run0006
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7500_7700.SplitTree.Run0007
open OwnerTree HexagonCover.NBand.M7500_7700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1005) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip0625_0645 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node0645 ![2244866514940266882360859903052801014001871091663233, 1238846733650231984268510722, 77919119024943183960068, 8769009824325699876222275622275337062960907444232, 182698855038962130087031371948671701637744656400, 2993155353253731711777011654710880546081278819434528, 1461501665234057007305356829503198254015922569280] HexagonCover.NBand.M7500_7700.SplitTree.Run0006.checked0645
def B0644 : Block := .branch 169 ![1496577676626844588240573268702064107938033629659521, 1238846733650231984268510722, 77937565769016893511684, 8769009824325699876222314307901564731094498041864, 182698855038962130087031371948671701637744656400, 2993155353253731711777011654710880546081278819434528, 1461501665234057007305666314513019599084647350336] ![Tip0625_0645, (.leaf 1 (Common.fact 783).pointIds 783), (.leaf 2 (Common.fact 732).pointIds 732), (.leaf 3 (Common.fact 460).pointIds 460), (.leaf 4 (Common.fact 461).pointIds 461), (.leaf 5 (Common.fact 462).pointIds 462), (.leaf 6 (Common.fact 463).pointIds 463)]
theorem treeEq0644 : B0644.tree = HexagonCover.NBand.M7500_7700.SplitData.node0644 := by
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

def B0643 : Block := .branch 90 ![1496577676626844588240573268702064107938033629659521, 906694364851709369386498, 77937565769016893511684, 8769009824325699876222314307901564731094498041864, 182698855038962130087031371948671701637744656400, 2993155353253731711777011654710880546081278819434528, 1461501665234057007305666314513019599084647350336] ![(.leaf 0 (Common.fact 781).pointIds 781), B0644, (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 782).pointIds 782)]
theorem treeEq0643 : B0643.tree = HexagonCover.NBand.M7500_7700.SplitData.node0643 := by
  change Tree.branch (90 : Fin 173) _ = Tree.branch (90 : Fin 173) _
  apply congrArg (Tree.branch (90 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0644
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0642 : Block := .branch 161 ![1496577676626844588240573268702064107938033629659521, 906694364851709369386498, 77937565769016893511684, 5846006549663894039814944642468998691782632955912, 182698855038962130087031371948671701637744656400, 2993155353253731711777011654710880546081278819434528, 1461501665234057007305666314513019599084647350336] ![(.leaf 0 (Common.fact 367).pointIds 367), (.leaf 1 (Common.fact 368).pointIds 368), (.leaf 2 (Common.fact 779).pointIds 779), B0643, (.leaf 4 (Common.fact 369).pointIds 369), (.leaf 5 (Common.fact 370).pointIds 370), (.leaf 6 (Common.fact 780).pointIds 780)]
theorem treeEq0642 : B0642.tree = HexagonCover.NBand.M7500_7700.SplitData.node0642 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0643
  · rfl
  · rfl
  · rfl

def B0641 : Block := .branch 162 ![1496577676626844588240573268702064107938033629659521, 906694364851709369386498, 77937565769016893511684, 340282367000205311603866613158902784008, 185553350424374049849147943887570691910510149648, 2993155353253731711777011654710880546081278819434528, 1461501665234057007305666314513019599084647350336] ![(.leaf 0 (Common.fact 372).pointIds 372), (.leaf 1 (Common.fact 373).pointIds 373), (.leaf 2 (Common.fact 374).pointIds 374), B0642, (.leaf 4 (Common.fact 637).pointIds 637), (.leaf 5 (Common.fact 375).pointIds 375), (.leaf 6 (Common.fact 778).pointIds 778)]
theorem treeEq0641 : B0641.tree = HexagonCover.NBand.M7500_7700.SplitData.node0641 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0642
  · rfl
  · rfl
  · rfl

def B0640 : Block := .branch 100 ![1496577676626844588240573268702064107938033629659521, 906694364851709369386498, 77937565769016893511684, 340282367000205311603866613158902784008, 185553350424374049849147943887570691910510149648, 2993155353253731711777011654710880546081278819434528, 1461501665234057006038015714284790197587944144960] ![(.leaf 0 (Common.fact 777).pointIds 777), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), B0641]
theorem treeEq0640 : B0640.tree = HexagonCover.NBand.M7500_7700.SplitData.node0640 := by
  change Tree.branch (100 : Fin 173) _ = Tree.branch (100 : Fin 173) _
  apply congrArg (Tree.branch (100 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0641

def B0639 : Block := .branch 159 ![1496577676626844588240573268702064107938033629659521, 906694364851709369386498, 77937565769016893511684, 340282367000205311603866613158902784008, 185553350424374049849147943887570691910510149648, 2993155353253731711777011654710880546081278819434528, 1461501665234057006038015714284790197587944144960] ![(.leaf 0 (Common.fact 775).pointIds 775), (.leaf 1 (Common.fact 776).pointIds 776), (.leaf 2 (Common.fact 499).pointIds 499), (.leaf 3 (Common.fact 500).pointIds 500), (.leaf 4 (Common.fact 501).pointIds 501), (.leaf 5 (Common.fact 502).pointIds 502), B0640]
theorem treeEq0639 : B0639.tree = HexagonCover.NBand.M7500_7700.SplitData.node0639 := by
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
  · exact treeEq0640

def B0638 : Block := .branch 168 ![1496577676626844588240573268702064107938033629659521, 906694364851709369386498, 77937565769016893511684, 340282367000205311603866613158902784008, 185553350424374049849147943887570691910510149648, 2993155353253731711777011654710880546081278819434528, 1461501665234057006038015714284790197587944144960] ![(.leaf 0 (Common.fact 774).pointIds 774), B0639, (.leaf 2 (Common.fact 749).pointIds 749), (.leaf 3 (Common.fact 492).pointIds 492), (.leaf 4 (Common.fact 493).pointIds 493), (.leaf 5 (Common.fact 494).pointIds 494), (.leaf 6 (Common.fact 495).pointIds 495)]
theorem treeEq0638 : B0638.tree = HexagonCover.NBand.M7500_7700.SplitData.node0638 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0639
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0637 : Block := .branch 170 ![590295810358705652097, 906694508966897445242370, 77937565769016893511684, 340282367000205311603866613158902784008, 185553350424374049849147943887570691910510149648, 2993155353253731711777011654710880546081278819434528, 1461501665234057006038015714284790197587944144960] ![B0638, (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 773).pointIds 773), (.leaf 6 (Common.fact 656).pointIds 656)]
theorem treeEq0637 : B0637.tree = HexagonCover.NBand.M7500_7700.SplitData.node0637 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0638
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0636 : Block := .branch 171 ![590295810358705652097, 906694508966897445242370, 77937565769016893511684, 340282367000205311603866613158902784008, 185553350424374049849147943887570691910510149648, 42535295865117307932921825928971419680, 1461501665234057006038015714284790197587944144960] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 727).pointIds 727), (.leaf 2 (Common.fact 728).pointIds 728), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 772).pointIds 772), B0637, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0636 : B0636.tree = HexagonCover.NBand.M7500_7700.SplitData.node0636 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0637
  · rfl

def B0635 : Block := .branch 143 ![590295810358705652097, 906694508966897445242370, 77937565769016893511684, 340282367000205311603866613158902784008, 185542200051774784537577176028434367729757159440, 42535295865117307932921825928971419680, 1461501665234057006038015714284790197587944144960] ![(.leaf 0 (Common.fact 565).pointIds 565), (.leaf 1 (Common.fact 566).pointIds 566), (.leaf 2 (Common.fact 567).pointIds 567), (.leaf 3 (Common.fact 568).pointIds 568), B0636, (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 771).pointIds 771)]
theorem treeEq0635 : B0635.tree = HexagonCover.NBand.M7500_7700.SplitData.node0635 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0636
  · rfl
  · rfl

def B0634 : Block := .branch 97 ![590295810358705652097, 906694508966897445242370, 77937565769016893511684, 340282367000205311603866613158902784008, 185542200051774784537577176028434367729757159440, 42535295865117307932921825928971419680, 1461501665234057006038015714284790197587944144960] ![(.leaf 0 (Common.fact 309).pointIds 309), (.leaf 1 (Common.fact 310).pointIds 310), (.leaf 2 (Common.fact 311).pointIds 311), B0635, (.leaf 4 (Common.fact 769).pointIds 769), (.leaf 5 (Common.fact 313).pointIds 313), (.leaf 6 (Common.fact 770).pointIds 770)]
theorem treeEq0634 : B0634.tree = HexagonCover.NBand.M7500_7700.SplitData.node0634 := by
  change Tree.branch (97 : Fin 173) _ = Tree.branch (97 : Fin 173) _
  apply congrArg (Tree.branch (97 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0635
  · rfl
  · rfl
  · rfl

def B0633 : Block := .branch 107 ![590295810358705652097, 906694508966897445242370, 77937565769016893511684, 340282367000205311603866613158902784008, 185542200051774784537577176028434367729757159440, 42535295865117307932921825928971419680, 1461501665234057006038015714284790197587944144960] ![(.leaf 0 (Common.fact 303).pointIds 303), (.leaf 1 (Common.fact 304).pointIds 304), (.leaf 2 (Common.fact 305).pointIds 305), B0634, (.leaf 4 (Common.fact 767).pointIds 767), (.leaf 5 (Common.fact 307).pointIds 307), (.leaf 6 (Common.fact 768).pointIds 768)]
theorem treeEq0633 : B0633.tree = HexagonCover.NBand.M7500_7700.SplitData.node0633 := by
  change Tree.branch (107 : Fin 173) _ = Tree.branch (107 : Fin 173) _
  apply congrArg (Tree.branch (107 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0634
  · rfl
  · rfl
  · rfl

def B0632 : Block := .branch 128 ![590295810358705652097, 906694508966897445242370, 77937565769016893511684, 79266848140492005727134572552, 185542200051774784537577176028434367729757159440, 42535295865117307932921825928971419680, 1461501665234057006038015714284790197587944144960] ![(.leaf 0 (Common.fact 291).pointIds 291), (.leaf 1 (Common.fact 292).pointIds 292), (.leaf 2 (Common.fact 293).pointIds 293), B0633, (.leaf 4 (Common.fact 765).pointIds 765), (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 6 (Common.fact 766).pointIds 766)]
theorem treeEq0632 : B0632.tree = HexagonCover.NBand.M7500_7700.SplitData.node0632 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0633
  · rfl
  · rfl
  · rfl

def B0631 : Block := .branch 129 ![590295810358705652097, 906694508966897445242370, 77937565769016893511684, 79266848140492005727134572552, 185542200051774784537577176028434367729757159440, 42535295865117307932921825928971419680, 1461501664553492272196138787358040982724407722048] ![(.leaf 0 (Common.fact 259).pointIds 259), (.leaf 1 (Common.fact 260).pointIds 260), (.leaf 2 (Common.fact 261).pointIds 261), (.leaf 3 (Common.fact 262).pointIds 262), (.leaf 4 (Common.fact 698).pointIds 698), (.leaf 5 (Common.fact 263).pointIds 263), B0632]
theorem treeEq0631 : B0631.tree = HexagonCover.NBand.M7500_7700.SplitData.node0631 := by
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
  · exact treeEq0632

def B0630 : Block := .branch 130 ![590295810358705652097, 906694508966897445242370, 77937565769016893511684, 79266848140492005727134572552, 185542200051774784537577176028434367729757159440, 42535295865117307932921825928971419680, 1461501664553492272196138787358040982724407722048] ![(.leaf 0 (Common.fact 252).pointIds 252), (.leaf 1 (Common.fact 253).pointIds 253), (.leaf 2 (Common.fact 254).pointIds 254), (.leaf 3 (Common.fact 255).pointIds 255), (.leaf 4 (Common.fact 697).pointIds 697), (.leaf 5 (Common.fact 256).pointIds 256), B0631]
theorem treeEq0630 : B0630.tree = HexagonCover.NBand.M7500_7700.SplitData.node0630 := by
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
  · exact treeEq0631

def B0629 : Block := .branch 118 ![590295810358705652097, 906694508966897445242370, 77937565769016893511684, 79266848140492005727134572552, 185542200051774784537577176028434367729757159440, 42535295865117307932921825928971419680, 1461501667275751207563646495065037842178553413696] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 298).pointIds 298), (.leaf 2 (Common.fact 299).pointIds 299), B0630, (.leaf 4 (Common.fact 763).pointIds 763), (.leaf 5 (Common.fact 301).pointIds 301), (.leaf 6 (Common.fact 764).pointIds 764)]
theorem treeEq0629 : B0629.tree = HexagonCover.NBand.M7500_7700.SplitData.node0629 := by
  change Tree.branch (118 : Fin 173) _ = Tree.branch (118 : Fin 173) _
  apply congrArg (Tree.branch (118 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0630
  · rfl
  · rfl
  · rfl

def B0628 : Block := .branch 131 ![590295810358705652097, 906694508966897445242370, 77937565769016893511684, 79266848140492005727134572552, 185542200051774784537577176028434367729757159440, 42535295865117307932921825928971419680, 1461501664553492272196138787358040982724407722048] ![(.leaf 0 (Common.fact 555).pointIds 555), (.leaf 1 (Common.fact 556).pointIds 556), (.leaf 2 (Common.fact 557).pointIds 557), (.leaf 3 (Common.fact 558).pointIds 558), (.leaf 4 (Common.fact 696).pointIds 696), (.leaf 5 (Common.fact 560).pointIds 560), B0629]
theorem treeEq0628 : B0628.tree = HexagonCover.NBand.M7500_7700.SplitData.node0628 := by
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
  · exact treeEq0629

def B0627 : Block := .branch 163 ![590295810358705652097, 906694508966897445242370, 77937565769016893511684, 79266848140492005727134572552, 185542200051774784537577176028434367729757159440, 42535295865117307932921825928971419680, 1461501664553492272196138787358040982724407722048] ![(.leaf 0 (Common.fact 280).pointIds 280), (.leaf 1 (Common.fact 281).pointIds 281), (.leaf 2 (Common.fact 282).pointIds 282), (.leaf 3 (Common.fact 283).pointIds 283), (.leaf 4 (Common.fact 595).pointIds 595), (.leaf 5 (Common.fact 284).pointIds 284), B0628]
theorem treeEq0627 : B0627.tree = HexagonCover.NBand.M7500_7700.SplitData.node0627 := by
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
  · exact treeEq0628

def B0626 : Block := .branch 151 ![590295810358705652097, 906694508966897445242370, 77937565769016893511684, 79266848140492005727134572552, 182687704666362864775460604089535377456991666192, 42535295865117307932921825928971419680, 1461501664553492272196138787358040982724407722048] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), B0627, (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 762).pointIds 762)]
theorem treeEq0626 : B0626.tree = HexagonCover.NBand.M7500_7700.SplitData.node0626 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0627
  · rfl
  · rfl

def B0625 : Block := .branch 160 ![590295810358705652097, 906694508966897445242370, 77937565769016893511684, 79266848140492005727134572552, 182687704666362864775460604089535377456991666192, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 362).pointIds 362), (.leaf 1 (Common.fact 761).pointIds 761), (.leaf 2 (Common.fact 735).pointIds 735), (.leaf 3 (Common.fact 363).pointIds 363), (.leaf 4 (Common.fact 364).pointIds 364), (.leaf 5 (Common.fact 365).pointIds 365), B0626]
theorem treeEq0625 : B0625.tree = HexagonCover.NBand.M7500_7700.SplitData.node0625 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0626

theorem accepted0625 : B0625.accepted = true := by decide +kernel
theorem checked0625 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node0625 (maskNeeds ![590295810358705652097, 906694508966897445242370, 77937565769016893511684, 79266848140492005727134572552, 182687704666362864775460604089535377456991666192, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072]) := by
  rw [← treeEq0625]
  exact B0625.sound accepted0625
#print axioms checked0625

def Tip0607_0625 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node0625 ![590295810358705652097, 906694508966897445242370, 77937565769016893511684, 79266848140492005727134572552, 182687704666362864775460604089535377456991666192, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] checked0625
def B0624 : Block := .branch 124 ![604462909807314587353473, 1538, 6148, 24584, 98320, 393248, 11869048958202650982480078096588602233847872] ![(.leaf 0 (Common.fact 759).pointIds 759), (.leaf 1 (Common.fact 173).pointIds 173), (.leaf 2 (Common.fact 174).pointIds 174), (.leaf 3 (Common.fact 175).pointIds 175), (.leaf 4 (Common.fact 176).pointIds 176), (.leaf 5 (Common.fact 177).pointIds 177), (.leaf 6 (Common.fact 760).pointIds 760)]
theorem treeEq0624 : B0624.tree = HexagonCover.NBand.M7500_7700.SplitData.node0624 := by
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

def B0623 : Block := .branch 143 ![604462909807314587353473, 1538, 6148, 24584, 2993339468206048245305803056293006609127943222427664, 42535295865117307932921825928971419680, 718676358937339411712218960264421480857664] ![(.leaf 0 (Common.fact 565).pointIds 565), (.leaf 1 (Common.fact 566).pointIds 566), (.leaf 2 (Common.fact 567).pointIds 567), (.leaf 3 (Common.fact 568).pointIds 568), (.leaf 4 (Common.fact 758).pointIds 758), (.leaf 5 (Common.fact 569).pointIds 569), B0624]
theorem treeEq0623 : B0623.tree = HexagonCover.NBand.M7500_7700.SplitData.node0623 := by
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
  · exact treeEq0624

def B0622 : Block := .branch 86 ![604462909807314587353473, 1538, 18482772870728521732, 24584, 2993339468206048245305803056293006609127943222427664, 42535295865117307932921825928971419680, 718676358937339411712218960264421480857664] ![(.leaf 0 (Common.fact 357).pointIds 357), (.leaf 1 (Common.fact 358).pointIds 358), (.leaf 2 (Common.fact 359).pointIds 359), B0623, (.leaf 4 (Common.fact 360).pointIds 360), (.leaf 5 (Common.fact 361).pointIds 361), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq0622 : B0622.tree = HexagonCover.NBand.M7500_7700.SplitData.node0622 := by
  change Tree.branch (86 : Fin 173) _ = Tree.branch (86 : Fin 173) _
  apply congrArg (Tree.branch (86 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0623
  · rfl
  · rfl
  · rfl

def B0621 : Block := .branch 89 ![604462909807314587353473, 1538, 18482772870728521732, 24584, 2993339468206048245305803056293006609127943222427664, 42535295865117307932921825928971419680, 718676358937339411712218960264421480857664] ![(.leaf 0 (Common.fact 70).pointIds 70), B0622, (.leaf 2 (Common.fact 72).pointIds 72), (.leaf 3 (Common.fact 73).pointIds 73), (.leaf 4 (Common.fact 74).pointIds 74), (.leaf 5 (Common.fact 75).pointIds 75), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq0621 : B0621.tree = HexagonCover.NBand.M7500_7700.SplitData.node0621 := by
  change Tree.branch (89 : Fin 173) _ = Tree.branch (89 : Fin 173) _
  apply congrArg (Tree.branch (89 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0622
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0620 : Block := .branch 100 ![604462909807314587353473, 1538, 18482772870728521732, 24584, 2993339468206048245305803056293006609127943222427664, 42535295865117307932921825928971419680, 718676358937339411712218960264421480857664] ![B0621, (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq0620 : B0620.tree = HexagonCover.NBand.M7500_7700.SplitData.node0620 := by
  change Tree.branch (100 : Fin 173) _ = Tree.branch (100 : Fin 173) _
  apply congrArg (Tree.branch (100 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0621
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0619 : Block := .branch 112 ![604462909807314587353473, 1538, 18482772870728521732, 24584, 2993339468206048245305803056293006609127943222427664, 42535295865117307932921825928971419680, 718676358937339411712218960264421480857664] ![B0620, (.leaf 1 (Common.fact 484).pointIds 484), (.leaf 2 (Common.fact 485).pointIds 485), (.leaf 3 (Common.fact 486).pointIds 486), (.leaf 4 (Common.fact 487).pointIds 487), (.leaf 5 (Common.fact 488).pointIds 488), (.leaf 6 (Common.fact 754).pointIds 754)]
theorem treeEq0619 : B0619.tree = HexagonCover.NBand.M7500_7700.SplitData.node0619 := by
  change Tree.branch (112 : Fin 173) _ = Tree.branch (112 : Fin 173) _
  apply congrArg (Tree.branch (112 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0620
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0618 : Block := .branch 128 ![604462909807314587353473, 1538, 18482772870728521732, 24584, 2993342322701433657225565172864945508118215987920912, 42535295865117307932921825928971419680, 718676358937339411712218960264421480857664] ![(.leaf 0 (Common.fact 291).pointIds 291), (.leaf 1 (Common.fact 292).pointIds 292), (.leaf 2 (Common.fact 293).pointIds 293), B0619, (.leaf 4 (Common.fact 752).pointIds 752), (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 6 (Common.fact 753).pointIds 753)]
theorem treeEq0618 : B0618.tree = HexagonCover.NBand.M7500_7700.SplitData.node0618 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0619
  · rfl
  · rfl
  · rfl

def B0617 : Block := .branch 90 ![604462909807314587353473, 1461501637330902918203685134947737923313226221058, 18482772870728521732, 24584, 2993342322701433657225565172864945508118215987920912, 42535295865117307932921825928971419680, 11692013822768100153703905789363218140577232584768] ![B0618, (.leaf 1 (Common.fact 750).pointIds 750), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 751).pointIds 751)]
theorem treeEq0617 : B0617.tree = HexagonCover.NBand.M7500_7700.SplitData.node0617 := by
  change Tree.branch (90 : Fin 173) _ = Tree.branch (90 : Fin 173) _
  apply congrArg (Tree.branch (90 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0618
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0616 : Block := .branch 168 ![604462909807314587353473, 1461501637330902918203685134947737923313226221058, 18554830464766449668, 38685626227668133590622216, 2993342322701433657225565172864945508118215987920912, 42535295865117307932921825928971419680, 11692013822768100153703905789363218140577232584768] ![B0617, (.leaf 1 (Common.fact 382).pointIds 382), (.leaf 2 (Common.fact 749).pointIds 749), (.leaf 3 (Common.fact 492).pointIds 492), (.leaf 4 (Common.fact 493).pointIds 493), (.leaf 5 (Common.fact 494).pointIds 494), (.leaf 6 (Common.fact 495).pointIds 495)]
theorem treeEq0616 : B0616.tree = HexagonCover.NBand.M7500_7700.SplitData.node0616 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0617
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0615 : Block := .branch 169 ![604462909807314587353473, 1461501637330902918203685134947737923313226221058, 18554830464766449668, 38685626227668133590622216, 2993342322701433657225565172864945508118215987920912, 42535295865117307932921825928971419680, 11692013822768100153703905789363218140577232584768] ![B0616, (.leaf 1 (Common.fact 748).pointIds 748), (.leaf 2 (Common.fact 732).pointIds 732), (.leaf 3 (Common.fact 460).pointIds 460), (.leaf 4 (Common.fact 461).pointIds 461), (.leaf 5 (Common.fact 462).pointIds 462), (.leaf 6 (Common.fact 463).pointIds 463)]
theorem treeEq0615 : B0615.tree = HexagonCover.NBand.M7500_7700.SplitData.node0615 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0616
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0614 : Block := .branch 160 ![604462909807314587353473, 302231454903657293678082, 18554830464766449668, 38685626227668133590622216, 2993342322701433657225565172864945508118215987920912, 42535295865117307932921825928971419680, 11692013822768100153703905789363218140577232584768] ![(.leaf 0 (Common.fact 362).pointIds 362), B0615, (.leaf 2 (Common.fact 735).pointIds 735), (.leaf 3 (Common.fact 363).pointIds 363), (.leaf 4 (Common.fact 364).pointIds 364), (.leaf 5 (Common.fact 365).pointIds 365), (.leaf 6 (Common.fact 747).pointIds 747)]
theorem treeEq0614 : B0614.tree = HexagonCover.NBand.M7500_7700.SplitData.node0614 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0615
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0613 : Block := .branch 162 ![604462909807314587353473, 302231454903657293678082, 18554830464766449668, 38685626227668133590622216, 2993342322701433657225565172864945508118215987920912, 42535295865117307932921825928971419680, 11692013822768100153703905789363218140577232584768] ![(.leaf 0 (Common.fact 372).pointIds 372), (.leaf 1 (Common.fact 373).pointIds 373), (.leaf 2 (Common.fact 374).pointIds 374), B0614, (.leaf 4 (Common.fact 746).pointIds 746), (.leaf 5 (Common.fact 375).pointIds 375), (.leaf 6 (Common.fact 667).pointIds 667)]
theorem treeEq0613 : B0613.tree = HexagonCover.NBand.M7500_7700.SplitData.node0613 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0614
  · rfl
  · rfl
  · rfl

def B0612 : Block := .branch 139 ![604462909807314587353473, 302231454903657293678082, 18554830464766449668, 79266848140492005727134572552, 2993342322701433657225565172864945508118215987920912, 42535295865117307932921825928971419680, 11692013125869812699621932616372022120315935522880] ![(.leaf 0 (Common.fact 94).pointIds 94), (.leaf 1 (Common.fact 95).pointIds 95), (.leaf 2 (Common.fact 96).pointIds 96), (.leaf 3 (Common.fact 97).pointIds 97), (.leaf 4 (Common.fact 664).pointIds 664), (.leaf 5 (Common.fact 98).pointIds 98), B0613]
theorem treeEq0612 : B0612.tree = HexagonCover.NBand.M7500_7700.SplitData.node0612 := by
  change Tree.branch (139 : Fin 173) _ = Tree.branch (139 : Fin 173) _
  apply congrArg (Tree.branch (139 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0613

def B0611 : Block := .branch 151 ![604462909807314587353473, 302231454903657293678082, 18554830464766449668, 79266848140492005727134572552, 2993339468206048245305803056293006609127943222427664, 42535295865117307932921825928971419680, 11692013125869812699621932616372022120315935522880] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), B0612, (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 663).pointIds 663)]
theorem treeEq0611 : B0611.tree = HexagonCover.NBand.M7500_7700.SplitData.node0611 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0612
  · rfl
  · rfl

def B0610 : Block := .branch 163 ![604462909807314587353473, 302231454903657293678082, 18554830464766449668, 79266848140492005727134572552, 2993339468206048245305803056293006609127943222427664, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 280).pointIds 280), (.leaf 1 (Common.fact 281).pointIds 281), (.leaf 2 (Common.fact 282).pointIds 282), (.leaf 3 (Common.fact 283).pointIds 283), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 284).pointIds 284), B0611]
theorem treeEq0610 : B0610.tree = HexagonCover.NBand.M7500_7700.SplitData.node0610 := by
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
  · exact treeEq0611

def B0609 : Block := .branch 171 ![604462909807314587353473, 302231599159582857889282, 18554830464766449668, 79266848140492005727134572552, 184114952359068824656518890058984872593374412816, 1496577676626887123536438386009406733953603895427104, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 727).pointIds 727), (.leaf 2 (Common.fact 728).pointIds 728), (.leaf 3 (Common.fact 729).pointIds 729), B0610, (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0609 : B0609.tree = HexagonCover.NBand.M7500_7700.SplitData.node0609 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0610
  · rfl
  · rfl

def B0608 : Block := .branch 170 ![604462909807314587353473, 302231599159582857889282, 18554830464766449668, 79266848140492005727134572552, 184114952359068824656518890058984872593374412816, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 744).pointIds 744), (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), B0609, (.leaf 6 (Common.fact 656).pointIds 656)]
theorem treeEq0608 : B0608.tree = HexagonCover.NBand.M7500_7700.SplitData.node0608 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0609
  · rfl

def B0607 : Block := .branch 79 ![590295810358705652097, 302231599159582857889282, 77937601797813912475652, 79266848140492005727134572552, 184114952359068824656518890058984872593374412816, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![B0608, Tip0607_0625, (.leaf 2 (Common.fact 222).pointIds 222), (.leaf 3 (Common.fact 223).pointIds 223), (.leaf 4 (Common.fact 224).pointIds 224), (.leaf 5 (Common.fact 225).pointIds 225), (.leaf 6 (Common.fact 464).pointIds 464)]
theorem treeEq0607 : B0607.tree = HexagonCover.NBand.M7500_7700.SplitData.node0607 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0608
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0607 : B0607.accepted = true := by decide +kernel
theorem checked0607 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node0607 (maskNeeds ![590295810358705652097, 302231599159582857889282, 77937601797813912475652, 79266848140492005727134572552, 184114952359068824656518890058984872593374412816, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072]) := by
  rw [← treeEq0607]
  exact B0607.sound accepted0607
#print axioms checked0607

def Tip0599_0607 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node0607 ![590295810358705652097, 302231599159582857889282, 77937601797813912475652, 79266848140492005727134572552, 184114952359068824656518890058984872593374412816, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] checked0607
def B0675 : Block := .branch 100 ![21267650467859855013215526316597576065, 1538, 6148, 24584, 98320, 393248, 5986310706529836989179075013470035836327660476694592] ![(.leaf 0 (Common.fact 821).pointIds 821), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), (.leaf 6 (Common.fact 822).pointIds 822)]
theorem treeEq0675 : B0675.tree = HexagonCover.NBand.M7500_7700.SplitData.node0675 := by
  change Tree.branch (100 : Fin 173) _ = Tree.branch (100 : Fin 173) _
  apply congrArg (Tree.branch (100 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0674 : Block := .branch 124 ![2535301201046754613352112062849, 1538, 6148, 24584, 98320, 393248, 5986310706529836989179075013470035836327660476694592] ![B0675, (.leaf 1 (Common.fact 173).pointIds 173), (.leaf 2 (Common.fact 174).pointIds 174), (.leaf 3 (Common.fact 175).pointIds 175), (.leaf 4 (Common.fact 176).pointIds 176), (.leaf 5 (Common.fact 177).pointIds 177), (.leaf 6 (Common.fact 820).pointIds 820)]
theorem treeEq0674 : B0674.tree = HexagonCover.NBand.M7500_7700.SplitData.node0674 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0675
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0673 : Block := .branch 128 ![2535301201046754613352112062849, 1538, 6148, 24584, 185542200051774784537577176028434367729757159440, 393248, 5986310706529836989179075013470035836327660476694592] ![(.leaf 0 (Common.fact 291).pointIds 291), (.leaf 1 (Common.fact 292).pointIds 292), (.leaf 2 (Common.fact 293).pointIds 293), B0674, (.leaf 4 (Common.fact 765).pointIds 765), (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 6 (Common.fact 819).pointIds 819)]
theorem treeEq0673 : B0673.tree = HexagonCover.NBand.M7500_7700.SplitData.node0673 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0674
  · rfl
  · rfl
  · rfl

def B0672 : Block := .branch 172 ![10387129018270702011674344770503041, 302231455044394782033410, 21287614718654860498948, 38685626227668133590622216, 185542200051774784537577176028434367729757159440, 42535295865117307932921825928971419680, 22458636216781938664140587816960780664896] ![(.leaf 0 (Common.fact 813).pointIds 813), (.leaf 1 (Common.fact 814).pointIds 814), (.leaf 2 (Common.fact 815).pointIds 815), (.leaf 3 (Common.fact 816).pointIds 816), (.leaf 4 (Common.fact 817).pointIds 817), (.leaf 5 (Common.fact 818).pointIds 818), B0673]
theorem treeEq0672 : B0672.tree = HexagonCover.NBand.M7500_7700.SplitData.node0672 := by
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
  · exact treeEq0673

def B0671 : Block := .branch 101 ![10384593717070245552871351364092289, 302231455044394782033410, 21287614718654860498948, 38685626227668133590622216, 185542200051774784537577176028434367729757159440, 42535295865117307932921825928971419680, 27903154087833866729611638886243247849536] ![B0672, (.leaf 1 (Common.fact 626).pointIds 626), (.leaf 2 (Common.fact 627).pointIds 627), (.leaf 3 (Common.fact 628).pointIds 628), (.leaf 4 (Common.fact 629).pointIds 629), (.leaf 5 (Common.fact 630).pointIds 630), (.leaf 6 (Common.fact 812).pointIds 812)]
theorem treeEq0671 : B0671.tree = HexagonCover.NBand.M7500_7700.SplitData.node0671 := by
  change Tree.branch (101 : Fin 173) _ = Tree.branch (101 : Fin 173) _
  apply congrArg (Tree.branch (101 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0672
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0670 : Block := .branch 113 ![590295810358705652097, 302231455044394782033410, 21287614718654860498948, 38685626227668133590622216, 185542200051774784537577176028434367729757159440, 42535295865117307932921825928971419680, 27903154087833866729611638886243247849536] ![B0671, (.leaf 1 (Common.fact 240).pointIds 240), (.leaf 2 (Common.fact 241).pointIds 241), (.leaf 3 (Common.fact 242).pointIds 242), (.leaf 4 (Common.fact 243).pointIds 243), (.leaf 5 (Common.fact 244).pointIds 244), (.leaf 6 (Common.fact 811).pointIds 811)]
theorem treeEq0670 : B0670.tree = HexagonCover.NBand.M7500_7700.SplitData.node0670 := by
  change Tree.branch (113 : Fin 173) _ = Tree.branch (113 : Fin 173) _
  apply congrArg (Tree.branch (113 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0671
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0669 : Block := .branch 129 ![590295810358705652097, 302231455044394782033410, 21287614718654860498948, 79266848140492005727134572552, 185542200051774784537577176028434367729757159440, 42535295865117307932921825928971419680, 27222589353991989802684889671379711426624] ![(.leaf 0 (Common.fact 259).pointIds 259), (.leaf 1 (Common.fact 260).pointIds 260), (.leaf 2 (Common.fact 261).pointIds 261), (.leaf 3 (Common.fact 262).pointIds 262), (.leaf 4 (Common.fact 698).pointIds 698), (.leaf 5 (Common.fact 263).pointIds 263), B0670]
theorem treeEq0669 : B0669.tree = HexagonCover.NBand.M7500_7700.SplitData.node0669 := by
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
  · exact treeEq0670

def B0668 : Block := .branch 130 ![590295810358705652097, 302231455044394782033410, 21287614718654860498948, 79266848140492005727134572552, 185542200051774784537577176028434367729757159440, 42535295865117307932921825928971419680, 27222589353991989802684889671379711426624] ![(.leaf 0 (Common.fact 252).pointIds 252), (.leaf 1 (Common.fact 253).pointIds 253), (.leaf 2 (Common.fact 254).pointIds 254), (.leaf 3 (Common.fact 255).pointIds 255), (.leaf 4 (Common.fact 697).pointIds 697), (.leaf 5 (Common.fact 256).pointIds 256), B0669]
theorem treeEq0668 : B0668.tree = HexagonCover.NBand.M7500_7700.SplitData.node0668 := by
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
  · exact treeEq0669

def B0667 : Block := .branch 131 ![590295810358705652097, 302231455044394782033410, 21287614718654860498948, 79266848140492005727134572552, 185542200051774784537577176028434367729757159440, 42535295865117307932921825928971419680, 27222589353991989802684889671379711426624] ![(.leaf 0 (Common.fact 555).pointIds 555), (.leaf 1 (Common.fact 556).pointIds 556), (.leaf 2 (Common.fact 557).pointIds 557), (.leaf 3 (Common.fact 558).pointIds 558), (.leaf 4 (Common.fact 696).pointIds 696), (.leaf 5 (Common.fact 560).pointIds 560), B0668]
theorem treeEq0667 : B0667.tree = HexagonCover.NBand.M7500_7700.SplitData.node0667 := by
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
  · exact treeEq0668

def B0666 : Block := .branch 163 ![590295810358705652097, 302231455044394782033410, 21287614718654860498948, 79266848140492005727134572552, 185542200051774784537577176028434367729757159440, 42535295865117307932921825928971419680, 27222589353991989802684889671379711426624] ![(.leaf 0 (Common.fact 280).pointIds 280), (.leaf 1 (Common.fact 281).pointIds 281), (.leaf 2 (Common.fact 282).pointIds 282), (.leaf 3 (Common.fact 283).pointIds 283), (.leaf 4 (Common.fact 595).pointIds 595), (.leaf 5 (Common.fact 284).pointIds 284), B0667]
theorem treeEq0666 : B0666.tree = HexagonCover.NBand.M7500_7700.SplitData.node0666 := by
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
  · exact treeEq0667

def B0665 : Block := .branch 151 ![590295810358705652097, 302231455044394782033410, 21287614718654860498948, 79266848140492005727134572552, 182687704666362864775460604089535377456991666192, 42535295865117307932921825928971419680, 27222589353991989802684889671379711426624] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), B0666, (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 810).pointIds 810)]
theorem treeEq0665 : B0665.tree = HexagonCover.NBand.M7500_7700.SplitData.node0665 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0666
  · rfl
  · rfl

def B0606 : Block := .branch 76 ![590295810358705652097, 302231599159582857889282, 21306097491525589014532, 79266848140492005727134572552, 184114952359068824656518890058984872593374412816, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 743).pointIds 743), Tip0599_0607, (.leaf 3 (Common.fact 327).pointIds 327), (.leaf 4 (Common.fact 328).pointIds 328), (.leaf 5 (Common.fact 329).pointIds 329), B0665]
theorem treeEq0606 : B0606.tree = HexagonCover.NBand.M7500_7700.SplitData.node0606 := by
  change Tree.branch (76 : Fin 173) _ = Tree.branch (76 : Fin 173) _
  apply congrArg (Tree.branch (76 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0665

def B0605 : Block := .branch 150 ![590295810358705652097, 302231599159582857889282, 21306097491525589014532, 79266848140492005727134572552, 182687704666362864775460604089535377456991666192, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 737).pointIds 737), (.leaf 1 (Common.fact 738).pointIds 738), (.leaf 2 (Common.fact 739).pointIds 739), (.leaf 3 (Common.fact 740).pointIds 740), B0606, (.leaf 5 (Common.fact 741).pointIds 741), (.leaf 6 (Common.fact 742).pointIds 742)]
theorem treeEq0605 : B0605.tree = HexagonCover.NBand.M7500_7700.SplitData.node0605 := by
  change Tree.branch (150 : Fin 173) _ = Tree.branch (150 : Fin 173) _
  apply congrArg (Tree.branch (150 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0606
  · rfl
  · rfl

def B0604 : Block := .branch 132 ![590295810358705652097, 302231599159582857889282, 21306097491525589014532, 79266848140492005727134572552, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 457).pointIds 457), (.leaf 5 (Common.fact 219).pointIds 219), B0605]
theorem treeEq0604 : B0604.tree = HexagonCover.NBand.M7500_7700.SplitData.node0604 := by
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
  · exact treeEq0605

def B0603 : Block := .branch 133 ![590295810358705652097, 302231599159582857889282, 21306097491525589014532, 79266848140492005727134572552, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 193).pointIds 193), (.leaf 1 (Common.fact 194).pointIds 194), (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 456).pointIds 456), (.leaf 5 (Common.fact 198).pointIds 198), B0604]
theorem treeEq0603 : B0603.tree = HexagonCover.NBand.M7500_7700.SplitData.node0603 := by
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
  · exact treeEq0604

def B0602 : Block := .branch 157 ![590295810358705652097, 302231599159582857889282, 21306097491525589014532, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 188).pointIds 188), (.leaf 1 (Common.fact 189).pointIds 189), (.leaf 2 (Common.fact 190).pointIds 190), (.leaf 3 (Common.fact 191).pointIds 191), B0603, (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 0 [] 0)]
theorem treeEq0602 : B0602.tree = HexagonCover.NBand.M7500_7700.SplitData.node0602 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0603
  · rfl
  · rfl

def B0601 : Block := .branch 125 ![590295810358705652097, 302231599159582857889282, 21306097491525589014532, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 454).pointIds 454), (.leaf 1 (Common.fact 266).pointIds 266), (.leaf 2 (Common.fact 267).pointIds 267), (.leaf 3 (Common.fact 268).pointIds 268), (.leaf 4 (Common.fact 269).pointIds 269), B0602, (.leaf 6 (Common.fact 455).pointIds 455)]
theorem treeEq0601 : B0601.tree = HexagonCover.NBand.M7500_7700.SplitData.node0601 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0602
  · rfl

def B0600 : Block := .branch 149 ![590295810358705652097, 302231599159582857889282, 21306097491525589014532, 79266848140492005727134572552, 98320, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 77).pointIds 77), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), B0601, (.leaf 5 (Common.fact 80).pointIds 80), (.leaf 6 (Common.fact 453).pointIds 453)]
theorem treeEq0600 : B0600.tree = HexagonCover.NBand.M7500_7700.SplitData.node0600 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0601
  · rfl
  · rfl

def B0599 : Block := .branch 88 ![590295810358705652097, 302231599159582857889282, 21306097491525589014532, 79266848140492005727134572552, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 200).pointIds 200), (.leaf 1 (Common.fact 720).pointIds 720), (.leaf 2 (Common.fact 202).pointIds 202), (.leaf 3 (Common.fact 203).pointIds 203), (.leaf 4 (Common.fact 204).pointIds 204), (.leaf 5 (Common.fact 205).pointIds 205), B0600]
theorem treeEq0599 : B0599.tree = HexagonCover.NBand.M7500_7700.SplitData.node0599 := by
  change Tree.branch (88 : Fin 173) _ = Tree.branch (88 : Fin 173) _
  apply congrArg (Tree.branch (88 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0600

theorem accepted0599 : B0599.accepted = true := by decide +kernel
theorem checked0599 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node0599 (maskNeeds ![590295810358705652097, 302231599159582857889282, 21306097491525589014532, 79266848140492005727134572552, 98320, 393248, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0599]
  exact B0599.sound accepted0599
#print axioms checked0599

def B0692 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877320932304062383649012434389696576] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 833).pointIds 833)]
theorem treeEq0692 : B0692.tree = HexagonCover.NBand.M7500_7700.SplitData.node0692 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0691 : Block := .branch 100 ![1496577676626844598625166985771719364999026288099713, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 832).pointIds 832), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), B0692]
theorem treeEq0691 : B0691.tree = HexagonCover.NBand.M7500_7700.SplitData.node0691 := by
  change Tree.branch (100 : Fin 173) _ = Tree.branch (100 : Fin 173) _
  apply congrArg (Tree.branch (100 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0692

def B0690 : Block := .branch 170 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664653462155419610937686491200] ![B0691, (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 831).pointIds 831)]
theorem treeEq0690 : B0690.tree = HexagonCover.NBand.M7500_7700.SplitData.node0690 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0691
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0689 : Block := .branch 171 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 727).pointIds 727), (.leaf 2 (Common.fact 728).pointIds 728), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 830).pointIds 830), B0690, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0689 : B0689.tree = HexagonCover.NBand.M7500_7700.SplitData.node0689 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0690
  · rfl

def B0688 : Block := .branch 142 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B0689, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 829).pointIds 829)]
theorem treeEq0688 : B0688.tree = HexagonCover.NBand.M7500_7700.SplitData.node0688 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0689
  · rfl
  · rfl

def B0687 : Block := .branch 88 ![10384593717070245552871351364092289, 302231599159582857889282, 18518801667747485700, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 200).pointIds 200), (.leaf 1 (Common.fact 720).pointIds 720), (.leaf 2 (Common.fact 202).pointIds 202), (.leaf 3 (Common.fact 203).pointIds 203), (.leaf 4 (Common.fact 204).pointIds 204), (.leaf 5 (Common.fact 205).pointIds 205), B0688]
theorem treeEq0687 : B0687.tree = HexagonCover.NBand.M7500_7700.SplitData.node0687 := by
  change Tree.branch (88 : Fin 173) _ = Tree.branch (88 : Fin 173) _
  apply congrArg (Tree.branch (88 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0688

def B0697 : Block := .branch 125 ![590295810358705652097, 1538, 6148, 24584, 98320, 2854495385411919762116571938898990272765886496, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 454).pointIds 454), (.leaf 1 (Common.fact 266).pointIds 266), (.leaf 2 (Common.fact 267).pointIds 267), (.leaf 3 (Common.fact 268).pointIds 268), (.leaf 4 (Common.fact 269).pointIds 269), (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 844).pointIds 844)]
theorem treeEq0697 : B0697.tree = HexagonCover.NBand.M7500_7700.SplitData.node0697 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0696 : Block := .branch 151 ![590295810358705652097, 1538, 6148, 24584, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 842).pointIds 842), B0697, (.leaf 6 (Common.fact 843).pointIds 843)]
theorem treeEq0696 : B0696.tree = HexagonCover.NBand.M7500_7700.SplitData.node0696 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0697
  · rfl

def B0695 : Block := .branch 170 ![590295810358705652097, 144255925564212738, 18518801667747485700, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664344279377053169526255386688] ![B0696, (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 841).pointIds 841)]
theorem treeEq0695 : B0695.tree = HexagonCover.NBand.M7500_7700.SplitData.node0695 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0696
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0694 : Block := .branch 171 ![590295810358705652097, 144255925564212738, 18518801667747485700, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664499021881963842060617777216] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 727).pointIds 727), (.leaf 2 (Common.fact 728).pointIds 728), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 840).pointIds 840), B0695, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0694 : B0694.tree = HexagonCover.NBand.M7500_7700.SplitData.node0694 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0695
  · rfl

def B0693 : Block := .branch 172 ![10384593717070245552871351364092289, 148294669267544049154, 11861328496989279623172, 38704515693599612171477000, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664499021881963842060617777216] ![(.leaf 0 (Common.fact 834).pointIds 834), (.leaf 1 (Common.fact 835).pointIds 835), (.leaf 2 (Common.fact 836).pointIds 836), (.leaf 3 (Common.fact 837).pointIds 837), B0694, (.leaf 5 (Common.fact 838).pointIds 838), (.leaf 6 (Common.fact 839).pointIds 839)]
theorem treeEq0693 : B0693.tree = HexagonCover.NBand.M7500_7700.SplitData.node0693 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0694
  · rfl
  · rfl

def B0686 : Block := .branch 78 ![10384593717070245552871351364092289, 148294669267544049154, 11861328496989279623172, 79286209843071771272510726152, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 142).pointIds 142), B0687, (.leaf 2 (Common.fact 144).pointIds 144), (.leaf 3 (Common.fact 145).pointIds 145), (.leaf 4 (Common.fact 146).pointIds 146), (.leaf 5 (Common.fact 147).pointIds 147), B0693]
theorem treeEq0686 : B0686.tree = HexagonCover.NBand.M7500_7700.SplitData.node0686 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0687
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0693

def B0702 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877320931994652931691393279988334656] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq0702 : B0702.tree = HexagonCover.NBand.M7500_7700.SplitData.node0702 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0701 : Block := .branch 100 ![1496577676626844598625166985771719364999026288099713, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 832).pointIds 832), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), B0702]
theorem treeEq0701 : B0701.tree = HexagonCover.NBand.M7500_7700.SplitData.node0701 := by
  change Tree.branch (100 : Fin 173) _ = Tree.branch (100 : Fin 173) _
  apply congrArg (Tree.branch (100 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0702

def B0700 : Block := .branch 170 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664344052703461991783285129280] ![B0701, (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 846).pointIds 846)]
theorem treeEq0700 : B0700.tree = HexagonCover.NBand.M7500_7700.SplitData.node0700 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0701
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0699 : Block := .branch 171 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 727).pointIds 727), (.leaf 2 (Common.fact 728).pointIds 728), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 830).pointIds 830), B0700, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0699 : B0699.tree = HexagonCover.NBand.M7500_7700.SplitData.node0699 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0700
  · rfl

def B0698 : Block := .branch 142 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B0699, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq0698 : B0698.tree = HexagonCover.NBand.M7500_7700.SplitData.node0698 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0699
  · rfl
  · rfl

def B0685 : Block := .branch 76 ![10384593717070245552871351364092289, 443442574446896875010, 11861328496989279623172, 79286209843071771272510726152, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 828).pointIds 828), B0686, (.leaf 3 (Common.fact 327).pointIds 327), (.leaf 4 (Common.fact 328).pointIds 328), (.leaf 5 (Common.fact 329).pointIds 329), B0698]
theorem treeEq0685 : B0685.tree = HexagonCover.NBand.M7500_7700.SplitData.node0685 := by
  change Tree.branch (76 : Fin 173) _ = Tree.branch (76 : Fin 173) _
  apply congrArg (Tree.branch (76 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0686
  · rfl
  · rfl
  · rfl
  · exact treeEq0698

theorem accepted0685 : B0685.accepted = true := by decide +kernel
theorem checked0685 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node0685 (maskNeeds ![10384593717070245552871351364092289, 443442574446896875010, 11861328496989279623172, 79286209843071771272510726152, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672]) := by
  rw [← treeEq0685]
  exact B0685.sound accepted0685
#print axioms checked0685

end HexagonCover.NBand.M7500_7700.SplitTree.Run0007
