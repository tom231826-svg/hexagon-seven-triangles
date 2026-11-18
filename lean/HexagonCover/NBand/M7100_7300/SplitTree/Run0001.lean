import HexagonCover.NBand.M7100_7300.SplitData
import HexagonCover.NBand.M7100_7300.SplitTree.Run0000
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7100_7300.SplitTree.Run0001
open OwnerTree HexagonCover.NBand.M7100_7300

abbrev Block := Chunk (n := 173) (Certificate := Fin 933) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def B0190 : Block := .branch 172 ![1122433257470197249316524486022832370365145978765697, 1267650600818525212954920486402, 4384504911992708754611054500510032300402620241924, 5846006723548183536335309995365386419956235657224, 2993155359177324619840843309373372790427570873139216, 182698855038962130087031371948671701637744951328, 1497308427467968675916457513933929409746152434696256] ![(.leaf 0 (Common.fact 600).pointIds 600), (.leaf 1 (Common.fact 601).pointIds 601), (.leaf 2 (Common.fact 602).pointIds 602), (.leaf 3 (Common.fact 603).pointIds 603), (.leaf 4 (Common.fact 604).pointIds 604), (.leaf 5 (Common.fact 605).pointIds 605), (.leaf 6 (Common.fact 606).pointIds 606)]
theorem treeEq0190 : B0190.tree = HexagonCover.NBand.M7100_7300.SplitData.node0190 := by
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

def B0191 : Block := .branch 172 ![1122433257470197249316524486022832370365145978765697, 1267650600818525212954920486402, 1461501637330902918203684835077466261090755155972, 8769009998209989372742602289545497123000919547912, 2993155359177324619840843309373372790427570873139216, 182698855038962130087031371948671701637744951328, 1497308427467968675916457513933929409746152434696256] ![(.leaf 0 (Common.fact 600).pointIds 600), (.leaf 1 (Common.fact 601).pointIds 601), (.leaf 2 (Common.fact 607).pointIds 607), (.leaf 3 (Common.fact 608).pointIds 608), (.leaf 4 (Common.fact 604).pointIds 604), (.leaf 5 (Common.fact 605).pointIds 605), (.leaf 6 (Common.fact 606).pointIds 606)]
theorem treeEq0191 : B0191.tree = HexagonCover.NBand.M7100_7300.SplitData.node0191 := by
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

def B0189 : Block := .branch 161 ![1122433257470197249316524486022832370365145978765697, 1267650600818525212954920486402, 1461501637330902918203684835077466261090755155972, 5846006723548183536335309995365386419956235657224, 2993155359177324619840843309373372790427570873139216, 182698855038962130087031371948671701637744951328, 1509000440566615899586605546254086400686555915616320] ![(.leaf 0 (Common.fact 331).pointIds 331), (.leaf 1 (Common.fact 332).pointIds 332), B0190, B0191, (.leaf 4 (Common.fact 333).pointIds 333), (.leaf 5 (Common.fact 334).pointIds 334), (.leaf 6 (Common.fact 578).pointIds 578)]
theorem treeEq0189 : B0189.tree = HexagonCover.NBand.M7100_7300.SplitData.node0189 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0190
  · exact treeEq0191
  · rfl
  · rfl
  · rfl

def B0192 : Block := .branch 172 ![1122433257470197249316524486022832370365145978765697, 1267650600818525212954920486402, 77919046967349146032132, 5846006723548183536335309995365386419956235657224, 2993155359177324619840843309373372790427570873139216, 182698855038962130087031371948671701637744951328, 1498769929105299578834660889281635871420739642458176] ![(.leaf 0 (Common.fact 600).pointIds 600), (.leaf 1 (Common.fact 601).pointIds 601), (.leaf 2 (Common.fact 609).pointIds 609), (.leaf 3 (Common.fact 603).pointIds 603), (.leaf 4 (Common.fact 604).pointIds 604), (.leaf 5 (Common.fact 605).pointIds 605), (.leaf 6 (Common.fact 610).pointIds 610)]
theorem treeEq0192 : B0192.tree = HexagonCover.NBand.M7100_7300.SplitData.node0192 := by
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

def B0188 : Block := .branch 160 ![1122433257470197249316524486022832370365145978765697, 1268270175301077710406957401602, 77919046967349146032132, 5846006723548183536335309995365386419956235657224, 2993155359177324619840843309373372790427570873139216, 182698855038962130087031371948671701637744951328, 1509000440566615899586605546254086400686555915616320] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 513).pointIds 513), B0189, (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), B0192]
theorem treeEq0188 : B0188.tree = HexagonCover.NBand.M7100_7300.SplitData.node0188 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0189
  · rfl
  · rfl
  · rfl
  · exact treeEq0192

def B0193 : Block := .branch 172 ![1122433257470197249316524486022832370365145978765697, 1267650600818525212954920486402, 77919046967349146032132, 5846006549663894039735755165580962022322679603208, 2993155359003100047977322816080124991422505548873744, 182698855038962130087031371948671701637744951328, 1497308427467968675916457513933929409746152434696256] ![(.leaf 0 (Common.fact 600).pointIds 600), (.leaf 1 (Common.fact 601).pointIds 601), (.leaf 2 (Common.fact 609).pointIds 609), (.leaf 3 (Common.fact 611).pointIds 611), (.leaf 4 (Common.fact 612).pointIds 612), (.leaf 5 (Common.fact 605).pointIds 605), (.leaf 6 (Common.fact 606).pointIds 606)]
theorem treeEq0193 : B0193.tree = HexagonCover.NBand.M7100_7300.SplitData.node0193 := by
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

def B0187 : Block := .branch 137 ![1122433257470197249316524486022832370365145978765697, 1268270175301077710406957401602, 77919046967349146032132, 5846006549663894039735755165580962022322679603208, 2993155359177324619840843309373372790427570873139216, 182698855038962130087031371948671701637744951328, 1509000440566615899586605546254086400686555915616320] ![(.leaf 0 (Common.fact 256).pointIds 256), (.leaf 1 (Common.fact 257).pointIds 257), (.leaf 2 (Common.fact 258).pointIds 258), B0188, B0193, (.leaf 5 (Common.fact 260).pointIds 260), (.leaf 0 [] 0)]
theorem treeEq0187 : B0187.tree = HexagonCover.NBand.M7100_7300.SplitData.node0187 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0188
  · exact treeEq0193
  · rfl
  · rfl

def B0186 : Block := .branch 143 ![1122433257470197249316524486022832370365145978765697, 1268270175301077710406957401602, 77919046967349146032132, 5846006549663894039735755165580962022322679603208, 2993155359177324619840843309373372790427570873139216, 182687704666362864775460604089535377456991961120, 1509000440566615899586605546254086400686555915616320] ![(.leaf 0 (Common.fact 427).pointIds 427), (.leaf 1 (Common.fact 428).pointIds 428), (.leaf 2 (Common.fact 429).pointIds 429), (.leaf 3 (Common.fact 430).pointIds 430), (.leaf 4 (Common.fact 599).pointIds 599), B0187, (.leaf 6 (Common.fact 577).pointIds 577)]
theorem treeEq0186 : B0186.tree = HexagonCover.NBand.M7100_7300.SplitData.node0186 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0187
  · rfl

def B0185 : Block := .branch 125 ![1122433257470154714020659368714899448539217007739265, 1268270175301077710406957401602, 77919046967349146032132, 5846006549663894039735755165580962022322679603208, 2993155359177324619840843309373372790427570873139216, 185542243607917750417700499340384118996088520736, 1509000440566615899586922458904143458036930091417664] ![B0186, (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 598).pointIds 598), (.leaf 6 (Common.fact 180).pointIds 180)]
theorem treeEq0185 : B0185.tree = HexagonCover.NBand.M7100_7300.SplitData.node0185 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0186
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0184 : Block := .branch 151 ![1122433257470154714020659368714899448539217007739265, 1268270175301077710406957401602, 77919046967349146032132, 5846006549663894039735755165580962022322679603208, 2993155359177324619840843309373372790427570873139216, 182687748222505830655583927401485128723323027488, 1509000440566615899586922458904143458036930091417664] ![(.leaf 0 (Common.fact 250).pointIds 250), (.leaf 1 (Common.fact 251).pointIds 251), (.leaf 2 (Common.fact 252).pointIds 252), (.leaf 3 (Common.fact 253).pointIds 253), (.leaf 4 (Common.fact 597).pointIds 597), B0185, (.leaf 6 (Common.fact 575).pointIds 575)]
theorem treeEq0184 : B0184.tree = HexagonCover.NBand.M7100_7300.SplitData.node0184 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0185
  · rfl

def B0183 : Block := .branch 169 ![374144419156732419900372734364162542475379545735553, 1268270175301077710406957401602, 77919046967349146032132, 5846006549663894039735755165580962022322679603208, 2993156072801170972820783838516357515175139064512528, 182687748222505830655583927401485128723323027488, 1509000440566615899586922458904143458036930091417664] ![B0184, (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 473).pointIds 473), (.leaf 3 (Common.fact 570).pointIds 570), (.leaf 4 (Common.fact 571).pointIds 571), (.leaf 5 (Common.fact 596).pointIds 596), (.leaf 6 (Common.fact 572).pointIds 572)]
theorem treeEq0183 : B0183.tree = HexagonCover.NBand.M7100_7300.SplitData.node0183 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0184
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0182 : Block := .branch 157 ![374144419156732419900372734364162542475379545735553, 1268270175301077710406957401602, 77919046967349146032132, 5846006549663894039735755165580962022322679603208, 2993156072801170972820783838516357515175139064512528, 43556142965880123323311949751266331459616, 1509000440566615899586922458904143458036930091417664] ![(.leaf 0 (Common.fact 202).pointIds 202), (.leaf 1 (Common.fact 203).pointIds 203), (.leaf 2 (Common.fact 204).pointIds 204), (.leaf 3 (Common.fact 205).pointIds 205), (.leaf 4 (Common.fact 595).pointIds 595), B0183, (.leaf 0 [] 0)]
theorem treeEq0182 : B0182.tree = HexagonCover.NBand.M7100_7300.SplitData.node0182 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0183
  · rfl

def B0181 : Block := .branch 171 ![374144419156732419900372734364162542475379545735553, 1268270175301077710406957401602, 77919046967349146032132, 5846006549663894039735755165580962022322679603208, 719547481796339637301113409890919789216497680, 233840262016500609878469696557917232896215538335776, 1509000440566615899586922458904143458036930091417664] ![(.leaf 0 (Common.fact 592).pointIds 592), (.leaf 1 (Common.fact 593).pointIds 593), (.leaf 2 (Common.fact 588).pointIds 588), (.leaf 3 (Common.fact 590).pointIds 590), B0182, (.leaf 5 (Common.fact 594).pointIds 594), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq0181 : B0181.tree = HexagonCover.NBand.M7100_7300.SplitData.node0181 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0182
  · rfl
  · rfl

theorem accepted0181 : B0181.accepted = true := by decide +kernel
theorem checked0181 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0181 (maskNeeds ![374144419156732419900372734364162542475379545735553, 1268270175301077710406957401602, 77919046967349146032132, 5846006549663894039735755165580962022322679603208, 719547481796339637301113409890919789216497680, 233840262016500609878469696557917232896215538335776, 1509000440566615899586922458904143458036930091417664]) := by
  rw [← treeEq0181]
  exact B0181.sound accepted0181
#print axioms checked0181

def Tip0161_0181 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0181 ![374144419156732419900372734364162542475379545735553, 1268270175301077710406957401602, 77919046967349146032132, 5846006549663894039735755165580962022322679603208, 719547481796339637301113409890919789216497680, 233840262016500609878469696557917232896215538335776, 1509000440566615899586922458904143458036930091417664] checked0181
def B0177 : Block := .branch 171 ![374144419156732419900372734364752838285738251387265, 1267651204691139209910802187778, 4384504911992708754611054500510032300402620241924, 5846006723548183536335309995365386419956235657224, 182699203488105857128017958444269711768393187344, 982129100286366761032876207585342189208786669273120, 1497308427467968675916457513933929409746152434696256] ![(.leaf 0 (Common.fact 579).pointIds 579), (.leaf 1 (Common.fact 580).pointIds 580), (.leaf 2 (Common.fact 581).pointIds 581), (.leaf 3 (Common.fact 582).pointIds 582), (.leaf 4 (Common.fact 583).pointIds 583), (.leaf 5 (Common.fact 584).pointIds 584), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq0177 : B0177.tree = HexagonCover.NBand.M7100_7300.SplitData.node0177 := by
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

def B0178 : Block := .branch 171 ![374144419156732419900372734364752838285738251387265, 1267651204691139209910802187778, 1461501637330902918203684835077466261090755155972, 8769009998209989372742602289545497123000919547912, 182699203488105857128017958444269711768393187344, 982129100286366761032876207585342189208786669273120, 1497308427467968675916457513933929409746152434696256] ![(.leaf 0 (Common.fact 579).pointIds 579), (.leaf 1 (Common.fact 580).pointIds 580), (.leaf 2 (Common.fact 586).pointIds 586), (.leaf 3 (Common.fact 587).pointIds 587), (.leaf 4 (Common.fact 583).pointIds 583), (.leaf 5 (Common.fact 584).pointIds 584), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq0178 : B0178.tree = HexagonCover.NBand.M7100_7300.SplitData.node0178 := by
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

def B0176 : Block := .branch 161 ![374144419156732419900372734364752838285738251387265, 1267651204691139209910802187778, 1461501637330902918203684835077466261090755155972, 5846006723548183536335309995365386419956235657224, 182699203488105857128017958444269711768393187344, 982129100286366761032876207585342189208786669273120, 1509000440566615899586605546254086400686555915616320] ![(.leaf 0 (Common.fact 331).pointIds 331), (.leaf 1 (Common.fact 332).pointIds 332), B0177, B0178, (.leaf 4 (Common.fact 333).pointIds 333), (.leaf 5 (Common.fact 334).pointIds 334), (.leaf 6 (Common.fact 578).pointIds 578)]
theorem treeEq0176 : B0176.tree = HexagonCover.NBand.M7100_7300.SplitData.node0176 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0177
  · exact treeEq0178
  · rfl
  · rfl
  · rfl

def B0179 : Block := .branch 171 ![374144419156732419900372734364752838285738251387265, 1267651204691139209910802187778, 77919046967349146032132, 5846006723548183536335309995365386419956235657224, 182699203488105857128017958444269711768393187344, 982129100286366761032876207585342189208786669273120, 1498769929105299578834660889281635871420739642458176] ![(.leaf 0 (Common.fact 579).pointIds 579), (.leaf 1 (Common.fact 580).pointIds 580), (.leaf 2 (Common.fact 588).pointIds 588), (.leaf 3 (Common.fact 582).pointIds 582), (.leaf 4 (Common.fact 583).pointIds 583), (.leaf 5 (Common.fact 584).pointIds 584), (.leaf 6 (Common.fact 589).pointIds 589)]
theorem treeEq0179 : B0179.tree = HexagonCover.NBand.M7100_7300.SplitData.node0179 := by
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

def B0175 : Block := .branch 160 ![374144419156732419900372734364752838285738251387265, 1268270174710781900048251749890, 77919046967349146032132, 5846006723548183536335309995365386419956235657224, 182699203488105857128017958444269711768393187344, 982129100286366761032876207585342189208786669273120, 1509000440566615899586605546254086400686555915616320] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 513).pointIds 513), B0176, (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), B0179]
theorem treeEq0175 : B0175.tree = HexagonCover.NBand.M7100_7300.SplitData.node0175 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0176
  · rfl
  · rfl
  · rfl
  · exact treeEq0179

def B0180 : Block := .branch 171 ![374144419156732419900372734364752838285738251387265, 1267651204691139209910802187778, 77919046967349146032132, 5846006549663894039735755165580962022322679603208, 182699029263533993607524665196470706703068921872, 982129100286366761032876207585342189208786669273120, 1497308427467968675916457513933929409746152434696256] ![(.leaf 0 (Common.fact 579).pointIds 579), (.leaf 1 (Common.fact 580).pointIds 580), (.leaf 2 (Common.fact 588).pointIds 588), (.leaf 3 (Common.fact 590).pointIds 590), (.leaf 4 (Common.fact 591).pointIds 591), (.leaf 5 (Common.fact 584).pointIds 584), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq0180 : B0180.tree = HexagonCover.NBand.M7100_7300.SplitData.node0180 := by
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

def B0174 : Block := .branch 137 ![374144419156732419900372734364752838285738251387265, 1268270174710781900048251749890, 77919046967349146032132, 5846006549663894039735755165580962022322679603208, 182699203488105857128017958444269711768393187344, 982129100286366761032876207585342189208786669273120, 1509000440566615899586605546254086400686555915616320] ![(.leaf 0 (Common.fact 256).pointIds 256), (.leaf 1 (Common.fact 257).pointIds 257), (.leaf 2 (Common.fact 258).pointIds 258), B0175, B0180, (.leaf 5 (Common.fact 260).pointIds 260), (.leaf 0 [] 0)]
theorem treeEq0174 : B0174.tree = HexagonCover.NBand.M7100_7300.SplitData.node0174 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0175
  · exact treeEq0180
  · rfl
  · rfl

def B0173 : Block := .branch 143 ![374144419156732419900372734364752838285738251387265, 1268270174710781900048251749890, 77919046967349146032132, 5846006549663894039735755165580962022322679603208, 182688053115506591816447190585133387587640197136, 982129100286366761032876207585342189208786669273120, 1509000440566615899586605546254086400686555915616320] ![(.leaf 0 (Common.fact 427).pointIds 427), (.leaf 1 (Common.fact 428).pointIds 428), (.leaf 2 (Common.fact 429).pointIds 429), (.leaf 3 (Common.fact 430).pointIds 430), B0174, (.leaf 5 (Common.fact 576).pointIds 576), (.leaf 6 (Common.fact 577).pointIds 577)]
theorem treeEq0173 : B0173.tree = HexagonCover.NBand.M7100_7300.SplitData.node0173 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0174
  · rfl
  · rfl

def B0172 : Block := .branch 151 ![374144419156732419900372734364752838285738251387265, 1268270174710781900048251749890, 77919046967349146032132, 5846006549663894039735755165580962022322679603208, 182688053115506591816447190585133387587640197136, 982129100286366761032876207585342189208786669273120, 1509000440566615899586605546254086400686555915616320] ![(.leaf 0 (Common.fact 250).pointIds 250), (.leaf 1 (Common.fact 251).pointIds 251), (.leaf 2 (Common.fact 252).pointIds 252), (.leaf 3 (Common.fact 253).pointIds 253), B0173, (.leaf 5 (Common.fact 574).pointIds 574), (.leaf 6 (Common.fact 575).pointIds 575)]
theorem treeEq0172 : B0172.tree = HexagonCover.NBand.M7100_7300.SplitData.node0172 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0173
  · rfl
  · rfl

def B0171 : Block := .branch 157 ![374144419156732419900372734364752838285738251387265, 1268270174710781900048251749890, 77919046967349146032132, 5846006549663894039735755165580962022322679603208, 348449143727040986586495598010130648629264, 982129100286366761032876207585342189208786669273120, 1509000440566615899586605546254086400686555915616320] ![(.leaf 0 (Common.fact 202).pointIds 202), (.leaf 1 (Common.fact 203).pointIds 203), (.leaf 2 (Common.fact 204).pointIds 204), (.leaf 3 (Common.fact 205).pointIds 205), B0172, (.leaf 5 (Common.fact 573).pointIds 573), (.leaf 0 [] 0)]
theorem treeEq0171 : B0171.tree = HexagonCover.NBand.M7100_7300.SplitData.node0171 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0172
  · rfl
  · rfl

def B0170 : Block := .branch 169 ![374144419156732419900372734364752838285738251387265, 1268270174710781900048251749890, 77919046967349146032132, 5846006549663894039735755165580962022322679603208, 713972295496706981515729480322757698840002576, 233840261972944466912589573234605283144949207269408, 1509000440566615899586605546254086400686555915616320] ![(.leaf 0 (Common.fact 569).pointIds 569), (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 473).pointIds 473), (.leaf 3 (Common.fact 570).pointIds 570), (.leaf 4 (Common.fact 571).pointIds 571), B0171, (.leaf 6 (Common.fact 572).pointIds 572)]
theorem treeEq0170 : B0170.tree = HexagonCover.NBand.M7100_7300.SplitData.node0170 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0171
  · rfl

def B0169 : Block := .branch 69 ![374144419156732419900372734364162542475379545735553, 1268270174710781900048251749890, 77919046967349146032132, 5846006549663894039735755165580962022322679603208, 719547481796339637301113409890919789216497680, 233840262016500609878469696557917232896215538335776, 1509000440566615899586922458904143458036930091417664] ![B0170, Tip0161_0181, (.leaf 2 (Common.fact 421).pointIds 421), (.leaf 3 (Common.fact 422).pointIds 422), (.leaf 4 (Common.fact 423).pointIds 423), (.leaf 5 (Common.fact 424).pointIds 424), (.leaf 6 (Common.fact 568).pointIds 568)]
theorem treeEq0169 : B0169.tree = HexagonCover.NBand.M7100_7300.SplitData.node0169 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0170
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0168 : Block := .branch 135 ![374144419156732419900372734364162542475379545735553, 1268270174710781900048251749890, 77919046967349146032132, 5846006549663894039735755165580962022322679603208, 719547481796339637301113409890919789216497680, 233840261972944466912589573234605283144949207269408, 1509000440566615899586922458904143458036930091417664] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), (.leaf 4 (Common.fact 419).pointIds 419), B0169, (.leaf 6 (Common.fact 567).pointIds 567)]
theorem treeEq0168 : B0168.tree = HexagonCover.NBand.M7100_7300.SplitData.node0168 := by
  change Tree.branch (135 : Fin 173) _ = Tree.branch (135 : Fin 173) _
  apply congrArg (Tree.branch (135 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0169
  · rfl

def B0167 : Block := .branch 138 ![374144419156732419900372734364162542475379545735553, 1268270174710781900048251749890, 77919046967349146032132, 5846006549663894039735793851207189690456270200840, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 1509000440566615899586922458904143458036930091417664] ![(.leaf 0 (Common.fact 116).pointIds 116), (.leaf 1 (Common.fact 117).pointIds 117), (.leaf 2 (Common.fact 118).pointIds 118), (.leaf 3 (Common.fact 119).pointIds 119), B0168, (.leaf 5 (Common.fact 120).pointIds 120), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq0167 : B0167.tree = HexagonCover.NBand.M7100_7300.SplitData.node0167 := by
  change Tree.branch (138 : Fin 173) _ = Tree.branch (138 : Fin 173) _
  apply congrArg (Tree.branch (138 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0168
  · rfl
  · rfl

def B0166 : Block := .branch 129 ![374144419156732419900372734364162542475379545735553, 1268270174710781900048251749890, 77919046967349146032132, 5846006549663894039735793851207189690456270200840, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 1509000440565935334853080581977216708822066554994752] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 298).pointIds 298), (.leaf 2 (Common.fact 299).pointIds 299), (.leaf 3 (Common.fact 300).pointIds 300), (.leaf 4 (Common.fact 565).pointIds 565), (.leaf 5 (Common.fact 301).pointIds 301), B0167]
theorem treeEq0166 : B0166.tree = HexagonCover.NBand.M7100_7300.SplitData.node0166 := by
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
  · exact treeEq0167

def B0165 : Block := .branch 130 ![374144419156732419900372734364162542475379545735553, 1268270174710781900048251749890, 77919046967349146032132, 5846006549663894039735793851207189690456270200840, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 1509000440565935334853080581977216708822066554994752] ![(.leaf 0 (Common.fact 559).pointIds 559), (.leaf 1 (Common.fact 560).pointIds 560), (.leaf 2 (Common.fact 561).pointIds 561), (.leaf 3 (Common.fact 562).pointIds 562), (.leaf 4 (Common.fact 563).pointIds 563), (.leaf 5 (Common.fact 564).pointIds 564), B0166]
theorem treeEq0165 : B0165.tree = HexagonCover.NBand.M7100_7300.SplitData.node0165 := by
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
  · exact treeEq0166

def B0164 : Block := .branch 100 ![374144419156732419902908035564619001278372952146305, 619574482552498551548544514, 77919046967349146032132, 5846006549663894039735793851207189690456270200840, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 1509000440568657593788448089684923705681520700686400] ![(.leaf 0 (Common.fact 557).pointIds 557), B0165, (.leaf 2 (Common.fact 453).pointIds 453), (.leaf 3 (Common.fact 454).pointIds 454), (.leaf 4 (Common.fact 455).pointIds 455), (.leaf 5 (Common.fact 456).pointIds 456), (.leaf 6 (Common.fact 558).pointIds 558)]
theorem treeEq0164 : B0164.tree = HexagonCover.NBand.M7100_7300.SplitData.node0164 := by
  change Tree.branch (100 : Fin 173) _ = Tree.branch (100 : Fin 173) _
  apply congrArg (Tree.branch (100 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0165
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0163 : Block := .branch 112 ![374144419156732414710611177029791372747876622926209, 619574482552498551548544514, 77919046967349146032132, 5846006549663894039735793851207189690456270200840, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 1509000440568657593788448089684923705681520700686400] ![B0164, (.leaf 1 (Common.fact 437).pointIds 437), (.leaf 2 (Common.fact 438).pointIds 438), (.leaf 3 (Common.fact 439).pointIds 439), (.leaf 4 (Common.fact 440).pointIds 440), (.leaf 5 (Common.fact 441).pointIds 441), (.leaf 6 (Common.fact 556).pointIds 556)]
theorem treeEq0163 : B0163.tree = HexagonCover.NBand.M7100_7300.SplitData.node0163 := by
  change Tree.branch (112 : Fin 173) _ = Tree.branch (112 : Fin 173) _
  apply congrArg (Tree.branch (112 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0164
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0162 : Block := .branch 162 ![374144419156732414710611177029791372747876622926209, 619574482552498551548544514, 77919046967349146032132, 340282366921054520342057611832540028936, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 1509000440568657593788448089684923705681520700686400] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), B0163, (.leaf 4 (Common.fact 554).pointIds 554), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 555).pointIds 555)]
theorem treeEq0162 : B0162.tree = HexagonCover.NBand.M7100_7300.SplitData.node0162 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0163
  · rfl
  · rfl
  · rfl

def B0161 : Block := .branch 131 ![374144419156732414710611177029791372747876622926209, 619574482552498551548544514, 77919046967349146032132, 340282366921054520342057611832540028936, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 1509000440565935334853080581977216708822066554994752] ![(.leaf 0 (Common.fact 548).pointIds 548), (.leaf 1 (Common.fact 549).pointIds 549), (.leaf 2 (Common.fact 550).pointIds 550), (.leaf 3 (Common.fact 551).pointIds 551), (.leaf 4 (Common.fact 552).pointIds 552), (.leaf 5 (Common.fact 553).pointIds 553), B0162]
theorem treeEq0161 : B0161.tree = HexagonCover.NBand.M7100_7300.SplitData.node0161 := by
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
  · exact treeEq0162

theorem accepted0161 : B0161.accepted = true := by decide +kernel
theorem checked0161 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0161 (maskNeeds ![374144419156732414710611177029791372747876622926209, 619574482552498551548544514, 77919046967349146032132, 340282366921054520342057611832540028936, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 1509000440565935334853080581977216708822066554994752]) := by
  rw [← treeEq0161]
  exact B0161.sound accepted0161
#print axioms checked0161

def Tip0092_0104 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0104 ![5192296859139290538337810916573569, 618970019642691236961191426, 77919046967349146032132, 174224571863520570664500254341332505485320, 11693440346339929630029090606126440435539863765008, 42535295865117307932921825928971419680, 16747358238029157353344982929643395798794304] HexagonCover.NBand.M7100_7300.SplitTree.Run0000.checked0104
def B0143 : Block := .branch 170 ![2535301804919368610307993764225, 618970019642691236961191426, 77919046967349146032132, 174224571863520570664500254341332505485320, 11693440346339929630029090606126440435539863765008, 42535295865117307932921825928971419680, 16747358243221454211879810558173892128014400] ![(.leaf 0 (Common.fact 509).pointIds 509), (.leaf 1 (Common.fact 507).pointIds 507), (.leaf 2 (Common.fact 501).pointIds 501), (.leaf 3 (Common.fact 499).pointIds 499), (.leaf 4 (Common.fact 510).pointIds 510), (.leaf 5 (Common.fact 511).pointIds 511), (.leaf 6 (Common.fact 512).pointIds 512)]
theorem treeEq0143 : B0143.tree = HexagonCover.NBand.M7100_7300.SplitData.node0143 := by
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

def B0103 : Block := .branch 112 ![2535301804919368610307993764225, 618970019642691236961191426, 77919046967349146032132, 174224571863520570664500254341332505485320, 11693440346339929630029090606126440435539863765008, 42535295865117307932921825928971419680, 16747358238029157353344982929643395798794304] ![Tip0092_0104, (.leaf 1 (Common.fact 437).pointIds 437), (.leaf 2 (Common.fact 438).pointIds 438), (.leaf 3 (Common.fact 439).pointIds 439), (.leaf 4 (Common.fact 440).pointIds 440), (.leaf 5 (Common.fact 441).pointIds 441), B0143]
theorem treeEq0103 : B0103.tree = HexagonCover.NBand.M7100_7300.SplitData.node0103 := by
  change Tree.branch (112 : Fin 173) _ = Tree.branch (112 : Fin 173) _
  apply congrArg (Tree.branch (112 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0143

def B0102 : Block := .branch 137 ![2535301804919368610307993764225, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 11693440346339929630029090606126440435539863765008, 42535295865117307932921825928971419680, 16747358238029157353344982929643395798794304] ![(.leaf 0 (Common.fact 256).pointIds 256), (.leaf 1 (Common.fact 257).pointIds 257), (.leaf 2 (Common.fact 258).pointIds 258), B0103, (.leaf 4 (Common.fact 436).pointIds 436), (.leaf 5 (Common.fact 260).pointIds 260), (.leaf 0 [] 0)]
theorem treeEq0102 : B0102.tree = HexagonCover.NBand.M7100_7300.SplitData.node0102 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0103
  · rfl
  · rfl
  · rfl

def B0101 : Block := .branch 163 ![2535301804919368610307993764225, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 1427247692706284399611944396176278292403421200, 42535295865117307932921825928971419680, 16747358238029157353344982929643395798794304] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B0102, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 435).pointIds 435)]
theorem treeEq0101 : B0101.tree = HexagonCover.NBand.M7100_7300.SplitData.node0101 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0102
  · rfl
  · rfl

def B0100 : Block := .branch 124 ![2535301804919368610307993764225, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 1427247692706284399611944396176278292403421200, 42535295865117307932921825928971419680, 16747336970381224794691016468730431313281088] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), (.leaf 4 (Common.fact 191).pointIds 191), (.leaf 5 (Common.fact 192).pointIds 192), B0101]
theorem treeEq0100 : B0100.tree = HexagonCover.NBand.M7100_7300.SplitData.node0100 := by
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
  · exact treeEq0101

def B0145 : Block := .branch 170 ![374144419156711147062678618376415207645270843064705, 619574482552498551548544514, 1461501637330902918203684835077466261090755155972, 77371252455336267181219848, 1427247692706284399611944396176278292403421200, 42535295865117307932921825928971419680, 16747336970381224794691016468730431313281088] ![(.leaf 0 (Common.fact 514).pointIds 514), (.leaf 1 (Common.fact 515).pointIds 515), (.leaf 2 (Common.fact 508).pointIds 508), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 517).pointIds 517), (.leaf 5 (Common.fact 511).pointIds 511), (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq0145 : B0145.tree = HexagonCover.NBand.M7100_7300.SplitData.node0145 := by
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

def B0144 : Block := .branch 160 ![374144419156711147062678618376415207645270843064705, 619574482552498551548544514, 2361183241434822612996, 77371252455336267181219848, 1427247692706284399611944396176278292403421200, 42535295865117307932921825928971419680, 16747336970381224794691016468730431313281088] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 513).pointIds 513), B0145, (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 446).pointIds 446)]
theorem treeEq0144 : B0144.tree = HexagonCover.NBand.M7100_7300.SplitData.node0144 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0145
  · rfl
  · rfl
  · rfl
  · rfl

def B0099 : Block := .branch 79 ![374144419156711147062678618376415207645270843064705, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 1427247692706284399611944396176278292403421200, 42535295865117307932921825928971419680, 16747336970381224794691016468730431313281088] ![B0100, B0144, (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), (.leaf 5 (Common.fact 224).pointIds 224), (.leaf 6 (Common.fact 433).pointIds 433)]
theorem treeEq0099 : B0099.tree = HexagonCover.NBand.M7100_7300.SplitData.node0099 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0100
  · exact treeEq0144
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0098 : Block := .branch 143 ![374144419156711147062678618376415207645270843064705, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 1427247692706284399611944396176278292403421200, 42535295865117307932921825928971419680, 5596964371115913223923157332406250560290880] ![(.leaf 0 (Common.fact 427).pointIds 427), (.leaf 1 (Common.fact 428).pointIds 428), (.leaf 2 (Common.fact 429).pointIds 429), (.leaf 3 (Common.fact 430).pointIds 430), (.leaf 4 (Common.fact 431).pointIds 431), (.leaf 5 (Common.fact 432).pointIds 432), B0099]
theorem treeEq0098 : B0098.tree = HexagonCover.NBand.M7100_7300.SplitData.node0098 := by
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
  · exact treeEq0099

def B0097 : Block := .branch 150 ![374144419156711147062678618376415207645270843064705, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 42535295865117307932921825928971419680, 5596964371115913223923157332406250560290880] ![(.leaf 0 (Common.fact 181).pointIds 181), (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), B0098, (.leaf 5 (Common.fact 185).pointIds 185), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq0097 : B0097.tree = HexagonCover.NBand.M7100_7300.SplitData.node0097 := by
  change Tree.branch (150 : Fin 173) _ = Tree.branch (150 : Fin 173) _
  apply congrArg (Tree.branch (150 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0098
  · rfl
  · rfl

def B0096 : Block := .branch 125 ![374144419156711147062678618376415207645270843064705, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 393248, 5596964371115913223923157332406250560290880] ![(.leaf 0 (Common.fact 426).pointIds 426), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), B0097, (.leaf 6 (Common.fact 180).pointIds 180)]
theorem treeEq0096 : B0096.tree = HexagonCover.NBand.M7100_7300.SplitData.node0096 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0097
  · rfl

def B0147 : Block := .branch 170 ![374144419156711147062678618375824911834912137412993, 618970609938501595666843138, 1461501637330902918203684835077466261090755155972, 77371252455336267181219848, 324518553658426726783156020674576, 43556142965880123323311949751266331459616, 5596964371115913223923157332406250560290880] ![(.leaf 0 (Common.fact 520).pointIds 520), (.leaf 1 (Common.fact 521).pointIds 521), (.leaf 2 (Common.fact 508).pointIds 508), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 522).pointIds 522), (.leaf 5 (Common.fact 523).pointIds 523), (.leaf 6 (Common.fact 524).pointIds 524)]
theorem treeEq0147 : B0147.tree = HexagonCover.NBand.M7100_7300.SplitData.node0147 := by
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

def B0146 : Block := .branch 160 ![374144419156711147062678618375824911834912137412993, 618970609938501595666843138, 2361183241434822612996, 77371252455336267181219848, 324518553658426726783156020674576, 43556142965880123323311949751266331459616, 5596964371115913223923157332406250560290880] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 519).pointIds 519), B0147, (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 446).pointIds 446)]
theorem treeEq0146 : B0146.tree = HexagonCover.NBand.M7100_7300.SplitData.node0146 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0147
  · rfl
  · rfl
  · rfl
  · rfl

def B0095 : Block := .branch 69 ![374144419156711147062678618375824911834912137412993, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 43556142965880123323311949751266331459616, 5596964371115913223923157332406250560290880] ![B0096, B0146, (.leaf 2 (Common.fact 421).pointIds 421), (.leaf 3 (Common.fact 422).pointIds 422), (.leaf 4 (Common.fact 423).pointIds 423), (.leaf 5 (Common.fact 424).pointIds 424), (.leaf 6 (Common.fact 425).pointIds 425)]
theorem treeEq0095 : B0095.tree = HexagonCover.NBand.M7100_7300.SplitData.node0095 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0096
  · exact treeEq0146
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0094 : Block := .branch 135 ![374144419156711147062678618375824911834912137412993, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 393248, 5596964371115913223923157332406250560290880] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), (.leaf 4 (Common.fact 419).pointIds 419), B0095, (.leaf 6 (Common.fact 420).pointIds 420)]
theorem treeEq0094 : B0094.tree = HexagonCover.NBand.M7100_7300.SplitData.node0094 := by
  change Tree.branch (135 : Fin 173) _ = Tree.branch (135 : Fin 173) _
  apply congrArg (Tree.branch (135 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0095
  · rfl

def B0093 : Block := .branch 168 ![2535301200456458802993406411137, 618970020002979207150831106, 77937529740219874547716, 116056878683004400771817480, 713623846353304459082801411451530724212047888, 393248, 5596964371115913223923157332406250560290880] ![B0094, (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 414).pointIds 414)]
theorem treeEq0093 : B0093.tree = HexagonCover.NBand.M7100_7300.SplitData.node0093 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0094
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0092 : Block := .branch 142 ![2535301200456458802993406411137, 618970020002979207150831106, 77937529740219874547716, 116056878683004400771817480, 713623846353304459082801411451530724212047888, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), (.leaf 4 (Common.fact 413).pointIds 413), (.leaf 5 (Common.fact 150).pointIds 150), B0093]
theorem treeEq0092 : B0092.tree = HexagonCover.NBand.M7100_7300.SplitData.node0092 := by
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
  · exact treeEq0093

theorem accepted0092 : B0092.accepted = true := by decide +kernel
theorem checked0092 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0092 (maskNeeds ![2535301200456458802993406411137, 618970020002979207150831106, 77937529740219874547716, 116056878683004400771817480, 713623846353304459082801411451530724212047888, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0092]
  exact B0092.sound accepted0092
#print axioms checked0092

def Tip0091_0161 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0161 ![374144419156732414710611177029791372747876622926209, 619574482552498551548544514, 77919046967349146032132, 340282366921054520342057611832540028936, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 1509000440565935334853080581977216708822066554994752] checked0161
def Tip0091_0092 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0092 ![2535301200456458802993406411137, 618970020002979207150831106, 77937529740219874547716, 116056878683004400771817480, 713623846353304459082801411451530724212047888, 393248, 21778071483257438539227764244160183795776] checked0092
def B0160 : Block := .branch 128 ![374144419156732414710611177029791372747876622926209, 619574482552498551548544514, 77919046967349146032132, 116056878683004400771817480, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 1509000440565935334853080581977216708822066554994752] ![(.leaf 0 (Common.fact 261).pointIds 261), (.leaf 1 (Common.fact 262).pointIds 262), (.leaf 2 (Common.fact 263).pointIds 263), Tip0091_0161, (.leaf 4 (Common.fact 546).pointIds 546), (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 547).pointIds 547)]
theorem treeEq0160 : B0160.tree = HexagonCover.NBand.M7100_7300.SplitData.node0160 := by
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

def B0159 : Block := .branch 139 ![374144419156732414710611177029791372747876622926209, 619574482552498551548544514, 77919046967349146032132, 116056878683004400771817480, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 1509000440565935334853080581977216708822066554994752] ![(.leaf 0 (Common.fact 110).pointIds 110), (.leaf 1 (Common.fact 111).pointIds 111), (.leaf 2 (Common.fact 112).pointIds 112), (.leaf 3 (Common.fact 113).pointIds 113), B0160, (.leaf 5 (Common.fact 114).pointIds 114), (.leaf 6 (Common.fact 545).pointIds 545)]
theorem treeEq0159 : B0159.tree = HexagonCover.NBand.M7100_7300.SplitData.node0159 := by
  change Tree.branch (139 : Fin 173) _ = Tree.branch (139 : Fin 173) _
  apply congrArg (Tree.branch (139 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0160
  · rfl
  · rfl

def B0158 : Block := .branch 159 ![374144419156732414710611177029791372747876622926209, 619574482552498551548544514, 77919046967349146032132, 116056878683004400771817480, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 1508269689747269883393978739560858567312238588723264] ![(.leaf 0 (Common.fact 543).pointIds 543), (.leaf 1 (Common.fact 544).pointIds 544), (.leaf 2 (Common.fact 228).pointIds 228), (.leaf 3 (Common.fact 229).pointIds 229), (.leaf 4 (Common.fact 230).pointIds 230), (.leaf 5 (Common.fact 231).pointIds 231), B0159]
theorem treeEq0158 : B0158.tree = HexagonCover.NBand.M7100_7300.SplitData.node0158 := by
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
  · exact treeEq0159

def B0157 : Block := .branch 79 ![374144419156732414710611177029791372747876622926209, 618970019642691236961191426, 77919046967349146032132, 116056878683004400771817480, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 1508269689747269883393978739560858567312238588723264] ![(.leaf 0 (Common.fact 541).pointIds 541), B0158, (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), (.leaf 5 (Common.fact 224).pointIds 224), (.leaf 6 (Common.fact 542).pointIds 542)]
theorem treeEq0157 : B0157.tree = HexagonCover.NBand.M7100_7300.SplitData.node0157 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0158
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0156 : Block := .branch 124 ![374144419156711147062678618375824911834912137412993, 618970019642691236961191426, 77919046967349146032132, 116056878683004400771817480, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 1508269689747269883393978739560858567312238588723264] ![B0157, (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), (.leaf 4 (Common.fact 191).pointIds 191), (.leaf 5 (Common.fact 192).pointIds 192), (.leaf 6 (Common.fact 540).pointIds 540)]
theorem treeEq0156 : B0156.tree = HexagonCover.NBand.M7100_7300.SplitData.node0156 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0157
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0155 : Block := .branch 163 ![374144419156711147062678618375824911834912137412993, 618970019642691236961191426, 77919046967349146032132, 116056878683004400771817480, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 1496577676648622660048349260899128303154991128379456] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 539).pointIds 539), (.leaf 5 (Common.fact 248).pointIds 248), B0156]
theorem treeEq0155 : B0155.tree = HexagonCover.NBand.M7100_7300.SplitData.node0155 := by
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
  · exact treeEq0156

def B0154 : Block := .branch 165 ![374144419156711147062678618375824911834912137412993, 618970019642691236961191426, 77919046967349146032132, 116056878683004400771817480, 719199032652612596314526914292909658567966736, 187072209578355573530071658587684226515959365894176, 1496577676648622660048349260899128303154991128379456] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 538).pointIds 538), B0155, (.leaf 0 [] 0)]
theorem treeEq0154 : B0154.tree = HexagonCover.NBand.M7100_7300.SplitData.node0154 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0155
  · rfl

def B0153 : Block := .branch 167 ![374144419156711147062678618375824911834912137412993, 618970019642691236961191426, 77919046967349146032132, 116056878683004400771817480, 719199032652612596314526914292909658567966736, 393248, 1496577676648622660048349260899128303154991128379456] ![(.leaf 0 (Common.fact 532).pointIds 532), (.leaf 1 (Common.fact 533).pointIds 533), (.leaf 2 (Common.fact 534).pointIds 534), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 536).pointIds 536), B0154, (.leaf 6 (Common.fact 537).pointIds 537)]
theorem treeEq0153 : B0153.tree = HexagonCover.NBand.M7100_7300.SplitData.node0153 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0154
  · rfl

def B0152 : Block := .branch 142 ![374144419156711147062678618375824911834912137412993, 618970019642691236961191426, 77919046967349146032132, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 1496577676648622660048349260899128303154991128379456] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), B0153, (.leaf 5 (Common.fact 150).pointIds 150), (.leaf 6 (Common.fact 531).pointIds 531)]
theorem treeEq0152 : B0152.tree = HexagonCover.NBand.M7100_7300.SplitData.node0152 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0153
  · rfl
  · rfl

def B0151 : Block := .branch 144 ![374144419156711147062678618375824911834912137412993, 618970019642691236961191426, 77919046967349146032132, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 1496577676648622660048349260899128303154991128379456] ![(.leaf 0 (Common.fact 134).pointIds 134), (.leaf 1 (Common.fact 135).pointIds 135), (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), B0152, (.leaf 6 (Common.fact 530).pointIds 530)]
theorem treeEq0151 : B0151.tree = HexagonCover.NBand.M7100_7300.SplitData.node0151 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0152
  · rfl

def B0150 : Block := .branch 170 ![374144419156711157447272335445480168895904795853185, 618970019642691236961191426, 77919046967349146032132, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 21778071807775992197654491027316204372032] ![(.leaf 0 (Common.fact 527).pointIds 527), (.leaf 1 (Common.fact 507).pointIds 507), (.leaf 2 (Common.fact 501).pointIds 501), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 528).pointIds 528), (.leaf 5 (Common.fact 529).pointIds 529), B0151]
theorem treeEq0150 : B0150.tree = HexagonCover.NBand.M7100_7300.SplitData.node0150 := by
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
  · exact treeEq0151

def B0149 : Block := .branch 113 ![374144419156711147062678618375824911834912137412993, 618970019642691236961191426, 77919046967349146032132, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 21778071807775992197654491027316204372032] ![B0150, (.leaf 1 (Common.fact 239).pointIds 239), (.leaf 2 (Common.fact 240).pointIds 240), (.leaf 3 (Common.fact 241).pointIds 241), (.leaf 4 (Common.fact 242).pointIds 242), (.leaf 5 (Common.fact 243).pointIds 243), (.leaf 6 (Common.fact 526).pointIds 526)]
theorem treeEq0149 : B0149.tree = HexagonCover.NBand.M7100_7300.SplitData.node0149 := by
  change Tree.branch (113 : Fin 173) _ = Tree.branch (113 : Fin 173) _
  apply congrArg (Tree.branch (113 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0150
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0148 : Block := .branch 168 ![2535301200456458802993406411137, 618970020002979207150831106, 77937529740219874547716, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 21778071807775992197654491027316204372032] ![B0149, (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 525).pointIds 525)]
theorem treeEq0148 : B0148.tree = HexagonCover.NBand.M7100_7300.SplitData.node0148 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0149
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0091 : Block := .branch 108 ![2535301200456458802993406411137, 618970020002979207150831106, 77937529740219874547716, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), Tip0091_0092, (.leaf 5 (Common.fact 308).pointIds 308), B0148]
theorem treeEq0091 : B0091.tree = HexagonCover.NBand.M7100_7300.SplitData.node0091 := by
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
  · exact treeEq0148

theorem accepted0091 : B0091.accepted = true := by decide +kernel
theorem checked0091 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0091 (maskNeeds ![2535301200456458802993406411137, 618970020002979207150831106, 77937529740219874547716, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0091]
  exact B0091.sound accepted0091
#print axioms checked0091

def Tip0090_0091 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0091 ![2535301200456458802993406411137, 618970020002979207150831106, 77937529740219874547716, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] checked0091
def B0206 : Block := .branch 170 ![374144419156711147060143317175368453031918731002241, 618970019642691236961191426, 77919046967349146032132, 174224571863520570664500254341332505485320, 11692015886240373486475925012121775021448669265936, 43556142965880123323311949751266331459616, 5596964371118448525123613791209243966701632] ![(.leaf 0 (Common.fact 626).pointIds 626), (.leaf 1 (Common.fact 507).pointIds 507), (.leaf 2 (Common.fact 501).pointIds 501), (.leaf 3 (Common.fact 499).pointIds 499), (.leaf 4 (Common.fact 627).pointIds 627), (.leaf 5 (Common.fact 523).pointIds 523), (.leaf 6 (Common.fact 628).pointIds 628)]
theorem treeEq0206 : B0206.tree = HexagonCover.NBand.M7100_7300.SplitData.node0206 := by
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

def B0205 : Block := .branch 108 ![374144419156711147060143317175368453031918731002241, 618970019642691236961191426, 77919046967349146032132, 174224571863520609350126482009466096082952, 11692015886240373161957371353695048238292648689680, 43556142965880123323311949751266331459616, 5596964371118448525123613791209243966701632] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), B0206, (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 625).pointIds 625)]
theorem treeEq0205 : B0205.tree = HexagonCover.NBand.M7100_7300.SplitData.node0205 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0206
  · rfl
  · rfl

def B0204 : Block := .branch 119 ![374144419156711147060143317175368453031918731002241, 618970019642691236961191426, 77919046967349146032132, 174224571863520609350126482009466096082952, 11692015886240373161957371353695048238292648689680, 43556142965880123323311949751266331459616, 5596964371118448525123613791209243966701632] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), B0205, (.leaf 5 (Common.fact 157).pointIds 157), (.leaf 6 (Common.fact 624).pointIds 624)]
theorem treeEq0204 : B0204.tree = HexagonCover.NBand.M7100_7300.SplitData.node0204 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0205
  · rfl
  · rfl

def B0203 : Block := .branch 129 ![374144419156711147060143317175368453031918731002241, 618970019642691236961191426, 77919046967349146032132, 174224571863520609350126482009466096082952, 11692015886240373161957371353695048238292648689680, 43556142965880123323311949751266331459616, 5596964371118448525123613791209243966701632] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 298).pointIds 298), (.leaf 2 (Common.fact 299).pointIds 299), (.leaf 3 (Common.fact 300).pointIds 300), B0204, (.leaf 5 (Common.fact 301).pointIds 301), (.leaf 6 (Common.fact 623).pointIds 623)]
theorem treeEq0203 : B0203.tree = HexagonCover.NBand.M7100_7300.SplitData.node0203 := by
  change Tree.branch (129 : Fin 173) _ = Tree.branch (129 : Fin 173) _
  apply congrArg (Tree.branch (129 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0204
  · rfl
  · rfl

def B0202 : Block := .branch 135 ![374144419156711147060143317175368453031918731002241, 618970019642691236961191426, 77919046967349146032132, 174224571863520609350126482009466096082952, 11692015886240373161957371353695048238292648689680, 393248, 5596964371118448525123613791209243966701632] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), (.leaf 4 (Common.fact 419).pointIds 419), B0203, (.leaf 6 (Common.fact 622).pointIds 622)]
theorem treeEq0202 : B0202.tree = HexagonCover.NBand.M7100_7300.SplitData.node0202 := by
  change Tree.branch (135 : Fin 173) _ = Tree.branch (135 : Fin 173) _
  apply congrArg (Tree.branch (135 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0203
  · rfl

def B0201 : Block := .branch 137 ![374144419156711147060143317175368453031918731002241, 618970019642691236961191426, 77919046967349146032132, 116056878683004400771817480, 11692015886240373161957371353695048238292648689680, 393248, 5596964371118448525123613791209243966701632] ![(.leaf 0 (Common.fact 256).pointIds 256), (.leaf 1 (Common.fact 257).pointIds 257), (.leaf 2 (Common.fact 258).pointIds 258), B0202, (.leaf 4 (Common.fact 621).pointIds 621), (.leaf 5 (Common.fact 260).pointIds 260), (.leaf 0 [] 0)]
theorem treeEq0201 : B0201.tree = HexagonCover.NBand.M7100_7300.SplitData.node0201 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0202
  · rfl
  · rfl
  · rfl

def B0200 : Block := .branch 141 ![374144419156711147060143317175368453031918731002241, 618970019642691236961191426, 77919046967349146032132, 116056878683004400771817480, 11692013098647223345629478661730264157247460442128, 393248, 5596964371118448525123613791209243966701632] ![(.leaf 0 (Common.fact 98).pointIds 98), (.leaf 1 (Common.fact 99).pointIds 99), (.leaf 2 (Common.fact 100).pointIds 100), (.leaf 3 (Common.fact 101).pointIds 101), B0201, (.leaf 5 (Common.fact 102).pointIds 102), (.leaf 6 (Common.fact 620).pointIds 620)]
theorem treeEq0200 : B0200.tree = HexagonCover.NBand.M7100_7300.SplitData.node0200 := by
  change Tree.branch (141 : Fin 173) _ = Tree.branch (141 : Fin 173) _
  apply congrArg (Tree.branch (141 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0201
  · rfl
  · rfl

def B0199 : Block := .branch 144 ![374144419156711147060143317175368453031918731002241, 618970019642691236961191426, 77919046967349146032132, 116056878683004400771817480, 11692013098647223345629478661730264157247460442128, 393248, 5596964371118448525123613791209243966701632] ![(.leaf 0 (Common.fact 134).pointIds 134), (.leaf 1 (Common.fact 135).pointIds 135), (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), B0200, (.leaf 6 (Common.fact 619).pointIds 619)]
theorem treeEq0199 : B0199.tree = HexagonCover.NBand.M7100_7300.SplitData.node0199 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0200
  · rfl

def B0198 : Block := .branch 128 ![374144419156711147060143317175368453031918731002241, 618970019642691236961191426, 77919046967349146032132, 116056878683004400771817480, 11692013098647223345629478661730264157247460442128, 393248, 5596964371118448525123613791209243966701632] ![(.leaf 0 (Common.fact 261).pointIds 261), (.leaf 1 (Common.fact 262).pointIds 262), (.leaf 2 (Common.fact 263).pointIds 263), B0199, (.leaf 4 (Common.fact 617).pointIds 617), (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 618).pointIds 618)]
theorem treeEq0198 : B0198.tree = HexagonCover.NBand.M7100_7300.SplitData.node0198 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0199
  · rfl
  · rfl
  · rfl

def B0197 : Block := .branch 97 ![374144419156711147060143317175368453031918731002241, 618970019642691236961191426, 77919046967349146032132, 116056878683004400771817480, 11692013098647223345629478661730264157247460442128, 393248, 5596964371118448525123613791209243966701632] ![(.leaf 0 (Common.fact 279).pointIds 279), (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 281).pointIds 281), B0198, (.leaf 4 (Common.fact 615).pointIds 615), (.leaf 5 (Common.fact 283).pointIds 283), (.leaf 6 (Common.fact 616).pointIds 616)]
theorem treeEq0197 : B0197.tree = HexagonCover.NBand.M7100_7300.SplitData.node0197 := by
  change Tree.branch (97 : Fin 173) _ = Tree.branch (97 : Fin 173) _
  apply congrArg (Tree.branch (97 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0198
  · rfl
  · rfl
  · rfl

def B0196 : Block := .branch 168 ![385, 618970020002979207150831106, 77937529740219874547716, 116056878683004400771817480, 11692726722493576325570007804714988904815651815440, 393248, 5596964371118448525123613791209243966701632] ![B0197, (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 614).pointIds 614)]
theorem treeEq0196 : B0196.tree = HexagonCover.NBand.M7100_7300.SplitData.node0196 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0197
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0195 : Block := .branch 142 ![385, 618970020002979207150831106, 77937529740219874547716, 116056878683004400771817480, 11692726722493576325570007804714988904815651815440, 393248, 21778071485792739739684223047153590206528] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), (.leaf 4 (Common.fact 539).pointIds 539), (.leaf 5 (Common.fact 150).pointIds 150), B0196]
theorem treeEq0195 : B0195.tree = HexagonCover.NBand.M7100_7300.SplitData.node0195 := by
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
  · exact treeEq0196

def B0194 : Block := .branch 163 ![385, 618970020002979207150831106, 77937529740219874547716, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 21778071485792739739684223047153590206528] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B0195, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 613).pointIds 613)]
theorem treeEq0194 : B0194.tree = HexagonCover.NBand.M7100_7300.SplitData.node0194 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0195
  · rfl
  · rfl

def B0090 : Block := .branch 101 ![385, 618970020002979207150831106, 77937529740219874547716, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![Tip0090_0091, (.leaf 1 (Common.fact 408).pointIds 408), (.leaf 2 (Common.fact 409).pointIds 409), (.leaf 3 (Common.fact 410).pointIds 410), (.leaf 4 (Common.fact 411).pointIds 411), (.leaf 5 (Common.fact 412).pointIds 412), B0194]
theorem treeEq0090 : B0090.tree = HexagonCover.NBand.M7100_7300.SplitData.node0090 := by
  change Tree.branch (101 : Fin 173) _ = Tree.branch (101 : Fin 173) _
  apply congrArg (Tree.branch (101 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0194

theorem accepted0090 : B0090.accepted = true := by decide +kernel
theorem checked0090 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0090 (maskNeeds ![385, 618970020002979207150831106, 77937529740219874547716, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0090]
  exact B0090.sound accepted0090
#print axioms checked0090

end HexagonCover.NBand.M7100_7300.SplitTree.Run0001
