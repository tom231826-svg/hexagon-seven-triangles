import HexagonCover.NBand.M8500_8700.SplitData
import HexagonCover.NBand.M8500_8700.SplitTree.Run0006
import HexagonCover.NBand.M8500_8700.SplitTree.Run0008
import HexagonCover.NBand.M8500_8700.SplitTree.Run0009
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8500_8700.SplitTree.Run0010
open OwnerTree HexagonCover.NBand.M8500_8700

abbrev Block := Chunk (n := 175) (Certificate := Fin 1173) (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck

def Tip0513_0517 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node0517 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 554601973303128821671506501640, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] HexagonCover.NBand.M8500_8700.SplitTree.Run0008.checked0517
def Tip0513_0692 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node0692 ![1238242271318996484309909889, 928681703055213498900416002, 9709203935524064268916740, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] HexagonCover.NBand.M8500_8700.SplitTree.Run0009.checked0692
def B0691 : Block := .branch 169 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 775).pointIds 775), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 823).pointIds 823), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq0691 : B0691.tree = HexagonCover.NBand.M8500_8700.SplitData.node0691 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0690 : Block := .branch 170 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 773).pointIds 773), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 821).pointIds 821), (.leaf 4 (Common.fact 749).pointIds 749), B0691, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq0690 : B0690.tree = HexagonCover.NBand.M8500_8700.SplitData.node0690 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0691
  · rfl

def B0689 : Block := .branch 163 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1329228312697565929961157434456244240, 233840261972944466912589573234605283144949207269408, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 731).pointIds 731), (.leaf 5 (Common.fact 387).pointIds 387), B0690]
theorem treeEq0689 : B0689.tree = HexagonCover.NBand.M8500_8700.SplitData.node0689 := by
  change Tree.branch (163 : Fin 175) _ = Tree.branch (163 : Fin 175) _
  apply congrArg (Tree.branch (163 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0690

def B0688 : Block := .branch 165 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1329228312697565929961157434456244240, 187072209578355573530071658587684226515959365894176, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 730).pointIds 730), B0689, (.leaf 0 [] 0)]
theorem treeEq0688 : B0688.tree = HexagonCover.NBand.M8500_8700.SplitData.node0688 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0689
  · rfl

def B0687 : Block := .branch 167 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1329228312697565929961157434456244240, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 729).pointIds 729), B0688, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq0687 : B0687.tree = HexagonCover.NBand.M8500_8700.SplitData.node0687 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0688
  · rfl

def B0516 : Block := .branch 98 ![1238242271318996484309909889, 226673591178292726072834, 9709203935524064268916740, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 275).pointIds 275), (.leaf 1 (Common.fact 276).pointIds 276), (.leaf 2 (Common.fact 277).pointIds 277), Tip0513_0517, B0687, (.leaf 5 (Common.fact 278).pointIds 278), (.leaf 6 (Common.fact 279).pointIds 279)]
theorem treeEq0516 : B0516.tree = HexagonCover.NBand.M8500_8700.SplitData.node0516 := by
  change Tree.branch (98 : Fin 175) _ = Tree.branch (98 : Fin 175) _
  apply congrArg (Tree.branch (98 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0687
  · rfl
  · rfl

def B0515 : Block := .branch 89 ![1238242271318996484309909889, 309711683412523361450853890, 9709203935524064268916740, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![B0516, Tip0513_0692, (.leaf 2 (Common.fact 270).pointIds 270), (.leaf 3 (Common.fact 271).pointIds 271), (.leaf 4 (Common.fact 272).pointIds 272), (.leaf 5 (Common.fact 273).pointIds 273), (.leaf 6 (Common.fact 274).pointIds 274)]
theorem treeEq0515 : B0515.tree = HexagonCover.NBand.M8500_8700.SplitData.node0515 := by
  change Tree.branch (89 : Fin 175) _ = Tree.branch (89 : Fin 175) _
  apply congrArg (Tree.branch (89 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0516
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0780 : Block := .branch 170 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1329227995784915872903807060280442896, 748288838313422294120286634350736906063837462396960, 2923014468633083363464181064536573941237675458624] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 773).pointIds 773), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 821).pointIds 821), (.leaf 4 (Common.fact 749).pointIds 749), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 860).pointIds 860)]
theorem treeEq0780 : B0780.tree = HexagonCover.NBand.M8500_8700.SplitData.node0780 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0779 : Block := .branch 169 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1329227995784915872903807060280442896, 393248, 2996078367722322259844610718467484198196587523473472] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 775).pointIds 775), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 823).pointIds 823), (.leaf 4 (Common.fact 754).pointIds 754), B0780, (.leaf 6 (Common.fact 859).pointIds 859)]
theorem treeEq0779 : B0779.tree = HexagonCover.NBand.M8500_8700.SplitData.node0779 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0780
  · rfl

def B0778 : Block := .branch 171 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 5986310706507378352962451535966627055644403482779656, 1329227995784915872903807060280442896, 393248, 2923014468633083363464181064536573941237675458624] ![(.leaf 0 (Common.fact 743).pointIds 743), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 824).pointIds 824), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B0779]
theorem treeEq0778 : B0778.tree = HexagonCover.NBand.M8500_8700.SplitData.node0778 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0779

def B0777 : Block := .branch 172 ![1238242271318996484309909889, 226673591178292726072834, 357879821537793192874743812, 158461160731807133703786749960, 1329227995784915872903807060280442896, 393248, 2923014468633083363464181064536573941237675458624] ![(.leaf 0 (Common.fact 740).pointIds 740), (.leaf 1 (Common.fact 769).pointIds 769), (.leaf 2 (Common.fact 858).pointIds 858), B0778, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 447).pointIds 447)]
theorem treeEq0777 : B0777.tree = HexagonCover.NBand.M8500_8700.SplitData.node0777 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0778
  · rfl
  · rfl
  · rfl

def B0776 : Block := .branch 161 ![1238242271318996484309909889, 226673591178292726072834, 357879821537793192874743812, 158461160731807133703786749960, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 396).pointIds 396), (.leaf 1 (Common.fact 397).pointIds 397), (.leaf 2 (Common.fact 856).pointIds 856), (.leaf 3 (Common.fact 857).pointIds 857), (.leaf 4 (Common.fact 398).pointIds 398), (.leaf 5 (Common.fact 399).pointIds 399), B0777]
theorem treeEq0776 : B0776.tree = HexagonCover.NBand.M8500_8700.SplitData.node0776 := by
  change Tree.branch (161 : Fin 175) _ = Tree.branch (161 : Fin 175) _
  apply congrArg (Tree.branch (161 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0777

def B0514 : Block := .branch 88 ![1238242271318996484309909889, 226673591178292726072834, 48394830163192197859514372, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 265).pointIds 265), B0515, B0776, (.leaf 3 (Common.fact 266).pointIds 266), (.leaf 4 (Common.fact 267).pointIds 267), (.leaf 5 (Common.fact 268).pointIds 268), (.leaf 6 (Common.fact 269).pointIds 269)]
theorem treeEq0514 : B0514.tree = HexagonCover.NBand.M8500_8700.SplitData.node0514 := by
  change Tree.branch (88 : Fin 175) _ = Tree.branch (88 : Fin 175) _
  apply congrArg (Tree.branch (88 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0515
  · exact treeEq0776
  · rfl
  · rfl
  · rfl
  · rfl

def B0783 : Block := .branch 169 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 775).pointIds 775), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 823).pointIds 823), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq0783 : B0783.tree = HexagonCover.NBand.M8500_8700.SplitData.node0783 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0782 : Block := .branch 170 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 773).pointIds 773), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 821).pointIds 821), (.leaf 4 (Common.fact 749).pointIds 749), B0783, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq0782 : B0782.tree = HexagonCover.NBand.M8500_8700.SplitData.node0782 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0783
  · rfl

def B0781 : Block := .branch 171 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158538531984262469970967945224, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 743).pointIds 743), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 861).pointIds 861), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B0782]
theorem treeEq0781 : B0781.tree = HexagonCover.NBand.M8500_8700.SplitData.node0781 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0782

def B0513 : Block := .branch 86 ![1238242271318996484309909889, 226673591178292726072834, 48394830163192197859514372, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 260).pointIds 260), (.leaf 1 (Common.fact 261).pointIds 261), B0514, B0781, (.leaf 4 (Common.fact 262).pointIds 262), (.leaf 5 (Common.fact 263).pointIds 263), (.leaf 6 (Common.fact 264).pointIds 264)]
theorem treeEq0513 : B0513.tree = HexagonCover.NBand.M8500_8700.SplitData.node0513 := by
  change Tree.branch (86 : Fin 175) _ = Tree.branch (86 : Fin 175) _
  apply congrArg (Tree.branch (86 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0514
  · exact treeEq0781
  · rfl
  · rfl
  · rfl

theorem accepted0513 : B0513.accepted = true := by decide +kernel
theorem checked0513 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node0513 (maskNeeds ![1238242271318996484309909889, 226673591178292726072834, 48394830163192197859514372, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq0513]
  exact B0513.sound accepted0513
#print axioms checked0513

def Tip0043_0045 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node0045 ![1238242271318996484309909889, 226673591178292726072834, 33887720327816647763040260, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448] HexagonCover.NBand.M8500_8700.SplitTree.Run0006.checked0045
def B0506 : Block := .branch 169 ![1238242271318996484309909889, 226673591178292726072834, 14544888767238507258189828, 89551429937849850484722238859788017643577352, 5846006549323611672814739330865132078623730270224, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 775).pointIds 775), (.leaf 2 (Common.fact 810).pointIds 810), (.leaf 3 (Common.fact 811).pointIds 811), (.leaf 4 (Common.fact 796).pointIds 796), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq0506 : B0506.tree = HexagonCover.NBand.M8500_8700.SplitData.node0506 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0505 : Block := .branch 170 ![1238242271318996484309909889, 226673591178292726072834, 14544888767238507258189828, 89551429937849850484722238859788017643577352, 5846006549323611672814739330865132078623730270224, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 773).pointIds 773), (.leaf 2 (Common.fact 808).pointIds 808), (.leaf 3 (Common.fact 809).pointIds 809), (.leaf 4 (Common.fact 792).pointIds 792), B0506, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq0505 : B0505.tree = HexagonCover.NBand.M8500_8700.SplitData.node0505 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0506
  · rfl

def B0504 : Block := .branch 171 ![1238242271318996484309909889, 226673591178292726072834, 14544888767238507258189828, 89551429937849850484722238859788017643577352, 5846006549323611672814739330865132078623730270224, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 743).pointIds 743), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 806).pointIds 806), (.leaf 3 (Common.fact 807).pointIds 807), (.leaf 4 (Common.fact 789).pointIds 789), (.leaf 5 (Common.fact 566).pointIds 566), B0505]
theorem treeEq0504 : B0504.tree = HexagonCover.NBand.M8500_8700.SplitData.node0504 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0505

def B0503 : Block := .branch 98 ![1238242271318996484309909889, 226673591178292726072834, 14544907213982580967741444, 89551429937849533572072181802437643467776008, 5846006549323611672814739330865132078623730270224, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 275).pointIds 275), (.leaf 1 (Common.fact 276).pointIds 276), (.leaf 2 (Common.fact 277).pointIds 277), B0504, (.leaf 4 (Common.fact 732).pointIds 732), (.leaf 5 (Common.fact 278).pointIds 278), (.leaf 6 (Common.fact 279).pointIds 279)]
theorem treeEq0503 : B0503.tree = HexagonCover.NBand.M8500_8700.SplitData.node0503 := by
  change Tree.branch (98 : Fin 175) _ = Tree.branch (98 : Fin 175) _
  apply congrArg (Tree.branch (98 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0504
  · rfl
  · rfl
  · rfl

def B0502 : Block := .branch 108 ![1238242271318996484309909889, 226673591178292726072834, 14544907213982580967741444, 89551429937849533572072181802437643467776008, 5846006549323611672814739330865132078623730270224, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), B0503, (.leaf 4 (Common.fact 712).pointIds 712), (.leaf 5 (Common.fact 288).pointIds 288), (.leaf 6 (Common.fact 289).pointIds 289)]
theorem treeEq0502 : B0502.tree = HexagonCover.NBand.M8500_8700.SplitData.node0502 := by
  change Tree.branch (108 : Fin 175) _ = Tree.branch (108 : Fin 175) _
  apply congrArg (Tree.branch (108 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0503
  · rfl
  · rfl
  · rfl

def B0501 : Block := .branch 119 ![1238242271318996484309909889, 226673591178292726072834, 14544907213982580967741444, 89551429937849533572072181802437643467776008, 5846006549323611672814739330865132078623730270224, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 310).pointIds 310), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), B0502, (.leaf 4 (Common.fact 786).pointIds 786), (.leaf 5 (Common.fact 313).pointIds 313), (.leaf 6 (Common.fact 314).pointIds 314)]
theorem treeEq0501 : B0501.tree = HexagonCover.NBand.M8500_8700.SplitData.node0501 := by
  change Tree.branch (119 : Fin 175) _ = Tree.branch (119 : Fin 175) _
  apply congrArg (Tree.branch (119 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0502
  · rfl
  · rfl
  · rfl

def B0500 : Block := .branch 129 ![1238242271318996484309909889, 226673591178292726072834, 14544907213982580967741444, 89551429937849533572072181802437643467776008, 5846006549323611672814739330865132078623730270224, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), (.leaf 2 (Common.fact 322).pointIds 322), B0501, (.leaf 4 (Common.fact 785).pointIds 785), (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 6 (Common.fact 324).pointIds 324)]
theorem treeEq0500 : B0500.tree = HexagonCover.NBand.M8500_8700.SplitData.node0500 := by
  change Tree.branch (129 : Fin 175) _ = Tree.branch (129 : Fin 175) _
  apply congrArg (Tree.branch (129 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0501
  · rfl
  · rfl
  · rfl

def B0499 : Block := .branch 138 ![1238242271318996484309909889, 226673591178292726072834, 14544907213982580967741444, 89202980794122492585485686204427512819245064, 5846006549323611672814739330865132078623730270224, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), B0500, (.leaf 4 (Common.fact 784).pointIds 784), (.leaf 5 (Common.fact 333).pointIds 333), (.leaf 6 (Common.fact 334).pointIds 334)]
theorem treeEq0499 : B0499.tree = HexagonCover.NBand.M8500_8700.SplitData.node0499 := by
  change Tree.branch (138 : Fin 175) _ = Tree.branch (138 : Fin 175) _
  apply congrArg (Tree.branch (138 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0500
  · rfl
  · rfl
  · rfl

def B0498 : Block := .branch 146 ![1238242271318996484309909889, 226673591178292726072834, 14544907213982580967741444, 19342813113834066795323400, 5846006549323611672814739330865132078623730270224, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 347).pointIds 347), B0499, (.leaf 4 (Common.fact 783).pointIds 783), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 0 [] 0)]
theorem treeEq0498 : B0498.tree = HexagonCover.NBand.M8500_8700.SplitData.node0498 := by
  change Tree.branch (146 : Fin 175) _ = Tree.branch (146 : Fin 175) _
  apply congrArg (Tree.branch (146 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0499
  · rfl
  · rfl
  · rfl

def B0497 : Block := .branch 162 ![1238242271318996484309909889, 226673591178292726072834, 14544907213982580967741444, 158475667841642509253883224072, 98320, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 373).pointIds 373), (.leaf 1 (Common.fact 374).pointIds 374), (.leaf 2 (Common.fact 375).pointIds 375), (.leaf 3 (Common.fact 805).pointIds 805), B0498, (.leaf 5 (Common.fact 376).pointIds 376), (.leaf 6 (Common.fact 377).pointIds 377)]
theorem treeEq0497 : B0497.tree = HexagonCover.NBand.M8500_8700.SplitData.node0497 := by
  change Tree.branch (162 : Fin 175) _ = Tree.branch (162 : Fin 175) _
  apply congrArg (Tree.branch (162 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0498
  · rfl
  · rfl

def B0044 : Block := .branch 84 ![1238242271318996484309909889, 226673591178292726072834, 14544907213982580967741444, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 250).pointIds 250), (.leaf 1 (Common.fact 251).pointIds 251), Tip0043_0045, B0497, (.leaf 4 (Common.fact 252).pointIds 252), (.leaf 5 (Common.fact 253).pointIds 253), (.leaf 6 (Common.fact 254).pointIds 254)]
theorem treeEq0044 : B0044.tree = HexagonCover.NBand.M8500_8700.SplitData.node0044 := by
  change Tree.branch (84 : Fin 175) _ = Tree.branch (84 : Fin 175) _
  apply congrArg (Tree.branch (84 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0497
  · rfl
  · rfl
  · rfl

def B0509 : Block := .branch 169 ![1238242271318996484309909889, 226673591178292726072834, 4873482210321473860540420, 158465996435085592220485574664, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 775).pointIds 775), (.leaf 2 (Common.fact 816).pointIds 816), (.leaf 3 (Common.fact 817).pointIds 817), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq0509 : B0509.tree = HexagonCover.NBand.M8500_8700.SplitData.node0509 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0508 : Block := .branch 170 ![1238242271318996484309909889, 226673591178292726072834, 4873482210321473860540420, 158465996435085592220485574664, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 773).pointIds 773), (.leaf 2 (Common.fact 814).pointIds 814), (.leaf 3 (Common.fact 815).pointIds 815), (.leaf 4 (Common.fact 749).pointIds 749), B0509, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq0508 : B0508.tree = HexagonCover.NBand.M8500_8700.SplitData.node0508 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0509
  · rfl

def B0507 : Block := .branch 171 ![1238242271318996484309909889, 226673591178292726072834, 4873482210321473860540420, 158465996435085592220485574664, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 743).pointIds 743), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 812).pointIds 812), (.leaf 3 (Common.fact 813).pointIds 813), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B0508]
theorem treeEq0507 : B0507.tree = HexagonCover.NBand.M8500_8700.SplitData.node0507 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0508

def B0043 : Block := .branch 83 ![1238242271318996484309909889, 226673591178292726072834, 4873500657065547570092036, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226643701663450043555079585443616680050752] ![(.leaf 0 (Common.fact 245).pointIds 245), (.leaf 1 (Common.fact 246).pointIds 246), B0044, B0507, (.leaf 4 (Common.fact 247).pointIds 247), (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 249).pointIds 249)]
theorem treeEq0043 : B0043.tree = HexagonCover.NBand.M8500_8700.SplitData.node0043 := by
  change Tree.branch (83 : Fin 175) _ = Tree.branch (83 : Fin 175) _
  apply congrArg (Tree.branch (83 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0044
  · exact treeEq0507
  · rfl
  · rfl
  · rfl

theorem accepted0043 : B0043.accepted = true := by decide +kernel
theorem checked0043 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node0043 (maskNeeds ![1238242271318996484309909889, 226673591178292726072834, 4873500657065547570092036, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226643701663450043555079585443616680050752]) := by
  rw [← treeEq0043]
  exact B0043.sound accepted0043
#print axioms checked0043

def B0809 : Block := .branch 169 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993886115266325905467305191218409773667103624659008] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 874).pointIds 874), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq0809 : B0809.tree = HexagonCover.NBand.M8500_8700.SplitData.node0809 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0808 : Block := .branch 170 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993886115266325905467305191218409773667103624659008] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 872).pointIds 872), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B0809, (.leaf 6 (Common.fact 750).pointIds 750)]
theorem treeEq0808 : B0808.tree = HexagonCover.NBand.M8500_8700.SplitData.node0808 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0809
  · rfl

def B0807 : Block := .branch 171 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 5986310706507378353287286997439407561319416980332552, 1329227995784915872903807060280442896, 393248, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 870).pointIds 870), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B0808]
theorem treeEq0807 : B0807.tree = HexagonCover.NBand.M8500_8700.SplitData.node0807 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0808

def B0806 : Block := .branch 172 ![1237940335011998006369059201, 377789318630121372911106, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 866).pointIds 866), (.leaf 1 (Common.fact 867).pointIds 867), (.leaf 2 (Common.fact 868).pointIds 868), B0807, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 503).pointIds 503)]
theorem treeEq0806 : B0806.tree = HexagonCover.NBand.M8500_8700.SplitData.node0806 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0807
  · rfl
  · rfl
  · rfl

def B0805 : Block := .branch 159 ![5192298715445182283218640147841409, 377789318630121372911106, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 363).pointIds 363), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), B0806]
theorem treeEq0805 : B0805.tree = HexagonCover.NBand.M8500_8700.SplitData.node0805 := by
  change Tree.branch (159 : Fin 175) _ = Tree.branch (159 : Fin 175) _
  apply congrArg (Tree.branch (159 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0806

def B0815 : Block := .branch 169 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993886115266325910659602049753237402197599953879104] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 874).pointIds 874), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 759).pointIds 759)]
theorem treeEq0815 : B0815.tree = HexagonCover.NBand.M8500_8700.SplitData.node0815 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0814 : Block := .branch 170 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993886115266325910659602049753237402197599953879104] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 872).pointIds 872), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B0815, (.leaf 6 (Common.fact 758).pointIds 758)]
theorem treeEq0814 : B0814.tree = HexagonCover.NBand.M8500_8700.SplitData.node0814 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0815
  · rfl

def B0813 : Block := .branch 171 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 5986310706507378353287286997439407561319416980332552, 1329227995784915872903807060280442896, 393248, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 870).pointIds 870), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B0814]
theorem treeEq0813 : B0813.tree = HexagonCover.NBand.M8500_8700.SplitData.node0813 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0814

def B0812 : Block := .branch 172 ![1237940335011998006369059201, 377789318630121372911106, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 866).pointIds 866), (.leaf 1 (Common.fact 867).pointIds 867), (.leaf 2 (Common.fact 868).pointIds 868), B0813, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq0812 : B0812.tree = HexagonCover.NBand.M8500_8700.SplitData.node0812 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0813
  · rfl
  · rfl
  · rfl

def B0811 : Block := .branch 159 ![10385863224580238141150633180266881, 377789318630121372911106, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 875).pointIds 875), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), B0812]
theorem treeEq0811 : B0811.tree = HexagonCover.NBand.M8500_8700.SplitData.node0811 := by
  change Tree.branch (159 : Fin 175) _ = Tree.branch (159 : Fin 175) _
  apply congrArg (Tree.branch (159 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0812

def B0819 : Block := .branch 169 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 874).pointIds 874), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq0819 : B0819.tree = HexagonCover.NBand.M8500_8700.SplitData.node0819 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0818 : Block := .branch 170 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 872).pointIds 872), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B0819, (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq0818 : B0818.tree = HexagonCover.NBand.M8500_8700.SplitData.node0818 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0819
  · rfl

def B0817 : Block := .branch 171 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 5986310706507378353287286997439407561319416980332552, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 870).pointIds 870), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B0818]
theorem treeEq0817 : B0817.tree = HexagonCover.NBand.M8500_8700.SplitData.node0817 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0818

def B0816 : Block := .branch 172 ![1237940335011998006369059201, 377789318630121372911106, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 866).pointIds 866), (.leaf 1 (Common.fact 867).pointIds 867), (.leaf 2 (Common.fact 868).pointIds 868), B0817, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq0816 : B0816.tree = HexagonCover.NBand.M8500_8700.SplitData.node0816 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0817
  · rfl
  · rfl
  · rfl

def B0810 : Block := .branch 113 ![1269507510582884089640521826689, 377789318630121372911106, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971282719353669933931636432422139592768] ![B0811, (.leaf 1 (Common.fact 300).pointIds 300), (.leaf 2 (Common.fact 301).pointIds 301), (.leaf 3 (Common.fact 302).pointIds 302), (.leaf 4 (Common.fact 303).pointIds 303), (.leaf 5 (Common.fact 304).pointIds 304), B0816]
theorem treeEq0810 : B0810.tree = HexagonCover.NBand.M8500_8700.SplitData.node0810 := by
  change Tree.branch (113 : Fin 175) _ = Tree.branch (113 : Fin 175) _
  apply congrArg (Tree.branch (113 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0811
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0816

def B0804 : Block := .branch 112 ![1269507510582884089640521826689, 377789318630121372911106, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![B0805, (.leaf 1 (Common.fact 295).pointIds 295), (.leaf 2 (Common.fact 296).pointIds 296), (.leaf 3 (Common.fact 297).pointIds 297), (.leaf 4 (Common.fact 298).pointIds 298), (.leaf 5 (Common.fact 299).pointIds 299), B0810]
theorem treeEq0804 : B0804.tree = HexagonCover.NBand.M8500_8700.SplitData.node0804 := by
  change Tree.branch (112 : Fin 175) _ = Tree.branch (112 : Fin 175) _
  apply congrArg (Tree.branch (112 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0805
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0810

def B0821 : Block := .branch 168 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 11193971278176093918715957461468237851525184] ![(.leaf 0 (Common.fact 876).pointIds 876), (.leaf 1 (Common.fact 877).pointIds 877), (.leaf 2 (Common.fact 841).pointIds 841), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 765).pointIds 765), (.leaf 6 (Common.fact 706).pointIds 706)]
theorem treeEq0821 : B0821.tree = HexagonCover.NBand.M8500_8700.SplitData.node0821 := by
  change Tree.branch (168 : Fin 175) _ = Tree.branch (168 : Fin 175) _
  apply congrArg (Tree.branch (168 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0820 : Block := .branch 170 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 11193971278176093918715957461468237851525184] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 872).pointIds 872), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B0821, (.leaf 6 (Common.fact 760).pointIds 760)]
theorem treeEq0820 : B0820.tree = HexagonCover.NBand.M8500_8700.SplitData.node0820 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0821
  · rfl

def B0803 : Block := .branch 109 ![1269507510582884089640521826689, 377789318630121372911106, 4873482210321473860540420, 325073150796026577146310828253192, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 290).pointIds 290), (.leaf 1 (Common.fact 291).pointIds 291), (.leaf 2 (Common.fact 292).pointIds 292), (.leaf 3 (Common.fact 293).pointIds 293), B0804, (.leaf 5 (Common.fact 294).pointIds 294), B0820]
theorem treeEq0803 : B0803.tree = HexagonCover.NBand.M8500_8700.SplitData.node0803 := by
  change Tree.branch (109 : Fin 175) _ = Tree.branch (109 : Fin 175) _
  apply congrArg (Tree.branch (109 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0804
  · rfl
  · exact treeEq0820

theorem accepted0803 : B0803.accepted = true := by decide +kernel
theorem checked0803 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node0803 (maskNeeds ![1269507510582884089640521826689, 377789318630121372911106, 4873482210321473860540420, 325073150796026577146310828253192, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672]) := by
  rw [← treeEq0803]
  exact B0803.sound accepted0803
#print axioms checked0803

def B0843 : Block := .branch 169 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993886115266325905467305191218409773667103624659008] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 874).pointIds 874), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq0843 : B0843.tree = HexagonCover.NBand.M8500_8700.SplitData.node0843 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0842 : Block := .branch 170 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993886115266325905467305191218409773667103624659008] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 872).pointIds 872), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B0843, (.leaf 6 (Common.fact 750).pointIds 750)]
theorem treeEq0842 : B0842.tree = HexagonCover.NBand.M8500_8700.SplitData.node0842 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0843
  · rfl

def B0841 : Block := .branch 171 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 5986310706507378353287286997439407561319416980332552, 1329227995784915872903807060280442896, 393248, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 870).pointIds 870), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B0842]
theorem treeEq0841 : B0841.tree = HexagonCover.NBand.M8500_8700.SplitData.node0841 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0842

def B0840 : Block := .branch 172 ![1237940335011998006369059201, 377789318630121372911106, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 866).pointIds 866), (.leaf 1 (Common.fact 867).pointIds 867), (.leaf 2 (Common.fact 868).pointIds 868), B0841, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 503).pointIds 503)]
theorem treeEq0840 : B0840.tree = HexagonCover.NBand.M8500_8700.SplitData.node0840 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0841
  · rfl
  · rfl
  · rfl

def B0839 : Block := .branch 159 ![5193565747075390869929999401484673, 377789318630121372911106, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 878).pointIds 878), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), B0840]
theorem treeEq0839 : B0839.tree = HexagonCover.NBand.M8500_8700.SplitData.node0839 := by
  change Tree.branch (159 : Fin 175) _ = Tree.branch (159 : Fin 175) _
  apply congrArg (Tree.branch (159 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0840

def B0849 : Block := .branch 169 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993886115266325910659602049753237402197599953879104] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 874).pointIds 874), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 759).pointIds 759)]
theorem treeEq0849 : B0849.tree = HexagonCover.NBand.M8500_8700.SplitData.node0849 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0848 : Block := .branch 170 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993886115266325910659602049753237402197599953879104] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 872).pointIds 872), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B0849, (.leaf 6 (Common.fact 758).pointIds 758)]
theorem treeEq0848 : B0848.tree = HexagonCover.NBand.M8500_8700.SplitData.node0848 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0849
  · rfl

def B0847 : Block := .branch 171 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 5986310706507378353287286997439407561319416980332552, 1329227995784915872903807060280442896, 393248, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 870).pointIds 870), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B0848]
theorem treeEq0847 : B0847.tree = HexagonCover.NBand.M8500_8700.SplitData.node0847 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0848

def B0846 : Block := .branch 172 ![1237940335011998006369059201, 377789318630121372911106, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 866).pointIds 866), (.leaf 1 (Common.fact 867).pointIds 867), (.leaf 2 (Common.fact 868).pointIds 868), B0847, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq0846 : B0846.tree = HexagonCover.NBand.M8500_8700.SplitData.node0846 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0847
  · rfl
  · rfl
  · rfl

def B0845 : Block := .branch 159 ![10385862605610218498460495730704769, 377789318630121372911106, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 879).pointIds 879), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), B0846]
theorem treeEq0845 : B0845.tree = HexagonCover.NBand.M8500_8700.SplitData.node0845 := by
  change Tree.branch (159 : Fin 175) _ = Tree.branch (159 : Fin 175) _
  apply congrArg (Tree.branch (159 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0846

def B0853 : Block := .branch 169 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 874).pointIds 874), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq0853 : B0853.tree = HexagonCover.NBand.M8500_8700.SplitData.node0853 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0852 : Block := .branch 170 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 872).pointIds 872), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B0853, (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq0852 : B0852.tree = HexagonCover.NBand.M8500_8700.SplitData.node0852 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0853
  · rfl

def B0851 : Block := .branch 171 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 5986310706507378353287286997439407561319416980332552, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 870).pointIds 870), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B0852]
theorem treeEq0851 : B0851.tree = HexagonCover.NBand.M8500_8700.SplitData.node0851 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0852

def B0850 : Block := .branch 172 ![1237940335011998006369059201, 377789318630121372911106, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 866).pointIds 866), (.leaf 1 (Common.fact 867).pointIds 867), (.leaf 2 (Common.fact 868).pointIds 868), B0851, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq0850 : B0850.tree = HexagonCover.NBand.M8500_8700.SplitData.node0850 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0851
  · rfl
  · rfl
  · rfl

def B0844 : Block := .branch 113 ![1268888540563241399503072264577, 377789318630121372911106, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971282719353669933931636432422139592768] ![B0845, (.leaf 1 (Common.fact 300).pointIds 300), (.leaf 2 (Common.fact 301).pointIds 301), (.leaf 3 (Common.fact 302).pointIds 302), (.leaf 4 (Common.fact 303).pointIds 303), (.leaf 5 (Common.fact 304).pointIds 304), B0850]
theorem treeEq0844 : B0844.tree = HexagonCover.NBand.M8500_8700.SplitData.node0844 := by
  change Tree.branch (113 : Fin 175) _ = Tree.branch (113 : Fin 175) _
  apply congrArg (Tree.branch (113 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0845
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0850

def B0838 : Block := .branch 112 ![1268888540563241399503072264577, 377789318630121372911106, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![B0839, (.leaf 1 (Common.fact 295).pointIds 295), (.leaf 2 (Common.fact 296).pointIds 296), (.leaf 3 (Common.fact 297).pointIds 297), (.leaf 4 (Common.fact 298).pointIds 298), (.leaf 5 (Common.fact 299).pointIds 299), B0844]
theorem treeEq0838 : B0838.tree = HexagonCover.NBand.M8500_8700.SplitData.node0838 := by
  change Tree.branch (112 : Fin 175) _ = Tree.branch (112 : Fin 175) _
  apply congrArg (Tree.branch (112 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0839
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0844

def B0855 : Block := .branch 168 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 11193971278176093918715957461468237851525184] ![(.leaf 0 (Common.fact 876).pointIds 876), (.leaf 1 (Common.fact 877).pointIds 877), (.leaf 2 (Common.fact 841).pointIds 841), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 765).pointIds 765), (.leaf 6 (Common.fact 706).pointIds 706)]
theorem treeEq0855 : B0855.tree = HexagonCover.NBand.M8500_8700.SplitData.node0855 := by
  change Tree.branch (168 : Fin 175) _ = Tree.branch (168 : Fin 175) _
  apply congrArg (Tree.branch (168 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0854 : Block := .branch 170 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 11193971278176093918715957461468237851525184] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 872).pointIds 872), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B0855, (.leaf 6 (Common.fact 760).pointIds 760)]
theorem treeEq0854 : B0854.tree = HexagonCover.NBand.M8500_8700.SplitData.node0854 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0855
  · rfl

def B0837 : Block := .branch 109 ![1268888540563241399503072264577, 377789318630121372911106, 4873482210321473860540420, 325073150796026577146310828253192, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 290).pointIds 290), (.leaf 1 (Common.fact 291).pointIds 291), (.leaf 2 (Common.fact 292).pointIds 292), (.leaf 3 (Common.fact 293).pointIds 293), B0838, (.leaf 5 (Common.fact 294).pointIds 294), B0854]
theorem treeEq0837 : B0837.tree = HexagonCover.NBand.M8500_8700.SplitData.node0837 := by
  change Tree.branch (109 : Fin 175) _ = Tree.branch (109 : Fin 175) _
  apply congrArg (Tree.branch (109 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0838
  · rfl
  · exact treeEq0854

theorem accepted0837 : B0837.accepted = true := by decide +kernel
theorem checked0837 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node0837 (maskNeeds ![1268888540563241399503072264577, 377789318630121372911106, 4873482210321473860540420, 325073150796026577146310828253192, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672]) := by
  rw [← treeEq0837]
  exact B0837.sound accepted0837
#print axioms checked0837

end HexagonCover.NBand.M8500_8700.SplitTree.Run0010
