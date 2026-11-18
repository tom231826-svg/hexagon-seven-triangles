import HexagonCover.NBand.M6700_6900.SplitData
import HexagonCover.NBand.M6700_6900.SplitTree.Run0001
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6700_6900.SplitTree.Run0002
open OwnerTree HexagonCover.NBand.M6700_6900

abbrev Block := Chunk (n := 175) (Certificate := Fin 929) (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck

def B0253 : Block := .branch 174 ![63802945065326562128765061894766592385, 2192252455996354377305527249074424530583410443778, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 14965776771843632182038388472398667689438839616667664, 5986493394212044715827068535409984783888156687990816, 2619010934119436665637785313558666805987011936649280] ![(.leaf 0 (Common.fact 699).pointIds 699), (.leaf 1 (Common.fact 700).pointIds 700), (.leaf 2 (Common.fact 701).pointIds 701), (.leaf 3 (Common.fact 702).pointIds 702), (.leaf 4 (Common.fact 703).pointIds 703), (.leaf 5 (Common.fact 704).pointIds 704), (.leaf 6 (Common.fact 705).pointIds 705)]
theorem treeEq0253 : B0253.tree = HexagonCover.NBand.M6700_6900.SplitData.node0253 := by
  change Tree.branch (174 : Fin 175) _ = Tree.branch (174 : Fin 175) _
  apply congrArg (Tree.branch (174 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0252 : Block := .branch 173 ![63802945065326562128765061894766592385, 2192252455996354377305527249074424530583410443778, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 2993155358828875476113802322786877192417440224608272, 5986493394212044715827068535409984783888156687990816, 2619010934119436665637785313558666805987011936649280] ![(.leaf 0 (Common.fact 693).pointIds 693), (.leaf 1 (Common.fact 694).pointIds 694), (.leaf 2 (Common.fact 695).pointIds 695), (.leaf 3 (Common.fact 696).pointIds 696), B0253, (.leaf 5 (Common.fact 697).pointIds 697), (.leaf 6 (Common.fact 698).pointIds 698)]
theorem treeEq0252 : B0252.tree = HexagonCover.NBand.M6700_6900.SplitData.node0252 := by
  change Tree.branch (173 : Fin 175) _ = Tree.branch (173 : Fin 175) _
  apply congrArg (Tree.branch (173 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0253
  · rfl
  · rfl

def B0251 : Block := .branch 172 ![63802945065326562128765061894766592385, 2192252455996354377305527249074424530583410443778, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 2993155359177324619840843309373372790427570873139216, 182687704666362864775460604089535377456991961120, 2619010934119436665637785313558666805987011936649280] ![(.leaf 0 (Common.fact 687).pointIds 687), (.leaf 1 (Common.fact 688).pointIds 688), (.leaf 2 (Common.fact 689).pointIds 689), (.leaf 3 (Common.fact 690).pointIds 690), (.leaf 4 (Common.fact 691).pointIds 691), B0252, (.leaf 6 (Common.fact 692).pointIds 692)]
theorem treeEq0251 : B0251.tree = HexagonCover.NBand.M6700_6900.SplitData.node0251 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0252
  · rfl

def B0254 : Block := .branch 174 ![63802945065326562128765061894766592385, 730750818665451459101842416358141510927477900802, 4384504911992708754611054500510032300402620241924, 5846006723548183536335309995365386419956235657224, 2993155359177324619840843309373372790427570873139216, 182698855038962130087031371948671701637744951328, 2619010934119436665637785313558666805987011936649280] ![(.leaf 0 (Common.fact 699).pointIds 699), (.leaf 1 (Common.fact 706).pointIds 706), (.leaf 2 (Common.fact 707).pointIds 707), (.leaf 3 (Common.fact 702).pointIds 702), (.leaf 4 (Common.fact 708).pointIds 708), (.leaf 5 (Common.fact 709).pointIds 709), (.leaf 6 (Common.fact 705).pointIds 705)]
theorem treeEq0254 : B0254.tree = HexagonCover.NBand.M6700_6900.SplitData.node0254 := by
  change Tree.branch (174 : Fin 175) _ = Tree.branch (174 : Fin 175) _
  apply congrArg (Tree.branch (174 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0255 : Block := .branch 174 ![63802945065326562128765061894766592385, 730750818665451459101842416358141510927477900802, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 2993155359177324619840843309373372790427570873139216, 182698855038962130087031371948671701637744951328, 1123894759129922980315415729689909276878992945184832] ![(.leaf 0 (Common.fact 699).pointIds 699), (.leaf 1 (Common.fact 706).pointIds 706), (.leaf 2 (Common.fact 701).pointIds 701), (.leaf 3 (Common.fact 702).pointIds 702), (.leaf 4 (Common.fact 708).pointIds 708), (.leaf 5 (Common.fact 709).pointIds 709), (.leaf 6 (Common.fact 710).pointIds 710)]
theorem treeEq0255 : B0255.tree = HexagonCover.NBand.M6700_6900.SplitData.node0255 := by
  change Tree.branch (174 : Fin 175) _ = Tree.branch (174 : Fin 175) _
  apply congrArg (Tree.branch (174 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0250 : Block := .branch 160 ![63802945065326562128765061894766592385, 730750818665451459101842416358141510927477900802, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 2993155359177324619840843309373372790427570873139216, 182698855038962130087031371948671701637744951328, 2619010934119436665637785313558666805987011936649280] ![(.leaf 0 (Common.fact 320).pointIds 320), B0251, B0254, (.leaf 3 (Common.fact 322).pointIds 322), (.leaf 4 (Common.fact 323).pointIds 323), (.leaf 5 (Common.fact 324).pointIds 324), B0255]
theorem treeEq0250 : B0250.tree = HexagonCover.NBand.M6700_6900.SplitData.node0250 := by
  change Tree.branch (160 : Fin 175) _ = Tree.branch (160 : Fin 175) _
  apply congrArg (Tree.branch (160 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0251
  · exact treeEq0254
  · rfl
  · rfl
  · rfl
  · exact treeEq0255

def B0256 : Block := .branch 174 ![63802945065326562128765061894766592385, 730750818665451459101842416358141510927477900802, 77919046967349146032132, 8769009998209989372742602289545497123000919547912, 2993155359177324619840843309373372790427570873139216, 182698855038962130087031371948671701637744951328, 2619010934119436665637785313558666805987011936649280] ![(.leaf 0 (Common.fact 699).pointIds 699), (.leaf 1 (Common.fact 706).pointIds 706), (.leaf 2 (Common.fact 711).pointIds 711), (.leaf 3 (Common.fact 712).pointIds 712), (.leaf 4 (Common.fact 708).pointIds 708), (.leaf 5 (Common.fact 709).pointIds 709), (.leaf 6 (Common.fact 705).pointIds 705)]
theorem treeEq0256 : B0256.tree = HexagonCover.NBand.M6700_6900.SplitData.node0256 := by
  change Tree.branch (174 : Fin 175) _ = Tree.branch (174 : Fin 175) _
  apply congrArg (Tree.branch (174 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0249 : Block := .branch 161 ![63802945065326562128765061894766592385, 730750818665451459101842416358141510927477900802, 77919046967349146032132, 5846006723548183536335309995365386419956235657224, 2993155359177324619840843309373372790427570873139216, 182698855038962130087031371948671701637744951328, 2619010934119436665962303867217093532770167957225536] ![(.leaf 0 (Common.fact 352).pointIds 352), (.leaf 1 (Common.fact 353).pointIds 353), B0250, B0256, (.leaf 4 (Common.fact 354).pointIds 354), (.leaf 5 (Common.fact 355).pointIds 355), (.leaf 6 (Common.fact 686).pointIds 686)]
theorem treeEq0249 : B0249.tree = HexagonCover.NBand.M6700_6900.SplitData.node0249 := by
  change Tree.branch (161 : Fin 175) _ = Tree.branch (161 : Fin 175) _
  apply congrArg (Tree.branch (161 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0250
  · exact treeEq0256
  · rfl
  · rfl
  · rfl

def B0257 : Block := .branch 174 ![63808136095772436767449571169291731329, 730750818665451459101842416358141510927477900802, 77919046967349146032132, 5846006723548183536335309995365386419956235657224, 2993155359177324619840843309373372790427570873139216, 182698855038962130087031371948671701637744951328, 2619010934119436665639052964158895035388508639854656] ![(.leaf 0 (Common.fact 713).pointIds 713), (.leaf 1 (Common.fact 706).pointIds 706), (.leaf 2 (Common.fact 711).pointIds 711), (.leaf 3 (Common.fact 702).pointIds 702), (.leaf 4 (Common.fact 708).pointIds 708), (.leaf 5 (Common.fact 709).pointIds 709), (.leaf 6 (Common.fact 714).pointIds 714)]
theorem treeEq0257 : B0257.tree = HexagonCover.NBand.M6700_6900.SplitData.node0257 := by
  change Tree.branch (174 : Fin 175) _ = Tree.branch (174 : Fin 175) _
  apply congrArg (Tree.branch (174 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0248 : Block := .branch 100 ![63808136095772436767449571169291731329, 730750818665451459101842416358141510927477900802, 77919046967349146032132, 5846006723548183536335309995365386419956235657224, 2993155359177324619840843309373372790427570873139216, 182698855038962130087031371948671701637744951328, 2619010934119436665962303867217093532770167957225536] ![B0249, (.leaf 1 (Common.fact 509).pointIds 509), (.leaf 2 (Common.fact 510).pointIds 510), (.leaf 3 (Common.fact 511).pointIds 511), (.leaf 4 (Common.fact 512).pointIds 512), (.leaf 5 (Common.fact 513).pointIds 513), B0257]
theorem treeEq0248 : B0248.tree = HexagonCover.NBand.M6700_6900.SplitData.node0248 := by
  change Tree.branch (100 : Fin 175) _ = Tree.branch (100 : Fin 175) _
  apply congrArg (Tree.branch (100 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0249
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0257

def B0258 : Block := .branch 174 ![63808136095772436767449571169291731329, 618970019642691236961191426, 77919046967349146032132, 5846006723548183536335309995365386419956235657224, 2993155359177324619840843309373372790427570873139216, 182698855038962130087031371948671701637744951328, 2619741684938102117096887155975024947496839902920768] ![(.leaf 0 (Common.fact 713).pointIds 713), (.leaf 1 (Common.fact 715).pointIds 715), (.leaf 2 (Common.fact 711).pointIds 711), (.leaf 3 (Common.fact 702).pointIds 702), (.leaf 4 (Common.fact 708).pointIds 708), (.leaf 5 (Common.fact 709).pointIds 709), (.leaf 6 (Common.fact 716).pointIds 716)]
theorem treeEq0258 : B0258.tree = HexagonCover.NBand.M6700_6900.SplitData.node0258 := by
  change Tree.branch (174 : Fin 175) _ = Tree.branch (174 : Fin 175) _
  apply congrArg (Tree.branch (174 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0247 : Block := .branch 159 ![93536104789241594903666902931066021632142380892545, 618970019642691236961191426, 77919046967349146032132, 5846006723548183536335309995365386419956235657224, 2993155359177324619840843309373372790427570873139216, 182698855038962130087031371948671701637744951328, 2619010934119436665962303867217093532770167957225536] ![(.leaf 0 (Common.fact 685).pointIds 685), B0248, (.leaf 2 (Common.fact 505).pointIds 505), (.leaf 3 (Common.fact 506).pointIds 506), (.leaf 4 (Common.fact 507).pointIds 507), (.leaf 5 (Common.fact 508).pointIds 508), B0258]
theorem treeEq0247 : B0247.tree = HexagonCover.NBand.M6700_6900.SplitData.node0247 := by
  change Tree.branch (159 : Fin 175) _ = Tree.branch (159 : Fin 175) _
  apply congrArg (Tree.branch (159 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0248
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0258

def B0259 : Block := .branch 174 ![63808136095772436767449571169291731329, 618970019642691236961191426, 77919046967349146032132, 5846006723548183536335309995365386419956235657224, 2993155353602138320208187523989443222265480496644112, 182693279852662497431245988019103539547368456224, 2619010934119436665637785313558666805987011936649280] ![(.leaf 0 (Common.fact 713).pointIds 713), (.leaf 1 (Common.fact 715).pointIds 715), (.leaf 2 (Common.fact 711).pointIds 711), (.leaf 3 (Common.fact 702).pointIds 702), (.leaf 4 (Common.fact 717).pointIds 717), (.leaf 5 (Common.fact 718).pointIds 718), (.leaf 6 (Common.fact 705).pointIds 705)]
theorem treeEq0259 : B0259.tree = HexagonCover.NBand.M6700_6900.SplitData.node0259 := by
  change Tree.branch (174 : Fin 175) _ = Tree.branch (174 : Fin 175) _
  apply congrArg (Tree.branch (174 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0246 : Block := .branch 142 ![93536104789241594903666902931066021632142380892545, 618970019642691236961191426, 77919046967349146032132, 5846006723548183536335309995365386419956235657224, 2993155353602138320208187523989443222265480496644112, 182698855038962130087031371948671701637744951328, 2619010934119436665962303867217093532770167957225536] ![(.leaf 0 (Common.fact 495).pointIds 495), (.leaf 1 (Common.fact 496).pointIds 496), (.leaf 2 (Common.fact 497).pointIds 497), (.leaf 3 (Common.fact 498).pointIds 498), B0247, B0259, (.leaf 6 (Common.fact 684).pointIds 684)]
theorem treeEq0246 : B0246.tree = HexagonCover.NBand.M6700_6900.SplitData.node0246 := by
  change Tree.branch (142 : Fin 175) _ = Tree.branch (142 : Fin 175) _
  apply congrArg (Tree.branch (142 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0247
  · exact treeEq0259
  · rfl

def B0260 : Block := .branch 174 ![63808136095772436767449571169291731329, 618970019642691236961191426, 77919046967349146032132, 5846006549663894039735755165580962022322679603208, 2993155353427913748344667030696195423260415172378640, 182698855038962130087031371948671701637744951328, 2619010934119436665637785313558666805987011936649280] ![(.leaf 0 (Common.fact 713).pointIds 713), (.leaf 1 (Common.fact 715).pointIds 715), (.leaf 2 (Common.fact 711).pointIds 711), (.leaf 3 (Common.fact 719).pointIds 719), (.leaf 4 (Common.fact 720).pointIds 720), (.leaf 5 (Common.fact 709).pointIds 709), (.leaf 6 (Common.fact 705).pointIds 705)]
theorem treeEq0260 : B0260.tree = HexagonCover.NBand.M6700_6900.SplitData.node0260 := by
  change Tree.branch (174 : Fin 175) _ = Tree.branch (174 : Fin 175) _
  apply congrArg (Tree.branch (174 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0245 : Block := .branch 137 ![93536104789241594903666902931066021632142380892545, 618970019642691236961191426, 77919046967349146032132, 5846006549663894039735755165580962022322679603208, 2993155353602138320208187523989443222265480496644112, 182698855038962130087031371948671701637744951328, 2619010934119436665962303867217093532770167957225536] ![(.leaf 0 (Common.fact 239).pointIds 239), (.leaf 1 (Common.fact 240).pointIds 240), (.leaf 2 (Common.fact 241).pointIds 241), B0246, B0260, (.leaf 5 (Common.fact 243).pointIds 243), (.leaf 0 [] 0)]
theorem treeEq0245 : B0245.tree = HexagonCover.NBand.M6700_6900.SplitData.node0245 := by
  change Tree.branch (137 : Fin 175) _ = Tree.branch (137 : Fin 175) _
  apply congrArg (Tree.branch (137 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0246
  · exact treeEq0260
  · rfl
  · rfl

def B0261 : Block := .branch 174 ![93536104789220327253199043076643101916184488968577, 618970019642691236961191426, 77919046967349146032132, 5846006549663894039735755165580962022322679603208, 2993155353602138320208187523989443222265480496644112, 182698855038962130087031371948671701637744951328, 2619010934119457933285717872212633266899976422162496] ![(.leaf 0 (Common.fact 721).pointIds 721), (.leaf 1 (Common.fact 715).pointIds 715), (.leaf 2 (Common.fact 711).pointIds 711), (.leaf 3 (Common.fact 719).pointIds 719), (.leaf 4 (Common.fact 717).pointIds 717), (.leaf 5 (Common.fact 709).pointIds 709), (.leaf 6 (Common.fact 722).pointIds 722)]
theorem treeEq0261 : B0261.tree = HexagonCover.NBand.M6700_6900.SplitData.node0261 := by
  change Tree.branch (174 : Fin 175) _ = Tree.branch (174 : Fin 175) _
  apply congrArg (Tree.branch (174 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0244 : Block := .branch 124 ![93536104789220327255734344277099560719177895379329, 618970019642691236961191426, 77919046967349146032132, 5846006549663894039735755165580962022322679603208, 2993155353602138320208187523989443222265480496644112, 182698855038962130087031371948671701637744951328, 2619010934119436665962303867217093532770167957225536] ![B0245, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 204).pointIds 204), B0261]
theorem treeEq0244 : B0244.tree = HexagonCover.NBand.M6700_6900.SplitData.node0244 := by
  change Tree.branch (124 : Fin 175) _ = Tree.branch (124 : Fin 175) _
  apply congrArg (Tree.branch (124 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0245
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0261

def B0262 : Block := .branch 174 ![93536104789220322060902184541815473385688159748481, 618970019642691236961191426, 77919046967349146032132, 5846006549663894039735755165580962022322679603208, 2993155353602138320208187523989443222265480496644112, 182698855038962130087031371948671701637744951328, 2619010934119436670830082172093494434517508265869376] ![(.leaf 0 (Common.fact 723).pointIds 723), (.leaf 1 (Common.fact 715).pointIds 715), (.leaf 2 (Common.fact 711).pointIds 711), (.leaf 3 (Common.fact 719).pointIds 719), (.leaf 4 (Common.fact 717).pointIds 717), (.leaf 5 (Common.fact 709).pointIds 709), (.leaf 6 (Common.fact 724).pointIds 724)]
theorem treeEq0262 : B0262.tree = HexagonCover.NBand.M6700_6900.SplitData.node0262 := by
  change Tree.branch (174 : Fin 175) _ = Tree.branch (174 : Fin 175) _
  apply congrArg (Tree.branch (174 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0243 : Block := .branch 112 ![93536104789220322063437485742271932188681566159233, 618970019642691236961191426, 77919046967349146032132, 5846006549663894039735755165580962022322679603208, 2993155353602138320208187523989443222265480496644112, 182698855038962130087031371948671701637744951328, 2619010934119436665962303867217093532770167957225536] ![B0244, (.leaf 1 (Common.fact 210).pointIds 210), (.leaf 2 (Common.fact 211).pointIds 211), (.leaf 3 (Common.fact 212).pointIds 212), (.leaf 4 (Common.fact 213).pointIds 213), (.leaf 5 (Common.fact 214).pointIds 214), B0262]
theorem treeEq0243 : B0243.tree = HexagonCover.NBand.M6700_6900.SplitData.node0243 := by
  change Tree.branch (112 : Fin 175) _ = Tree.branch (112 : Fin 175) _
  apply congrArg (Tree.branch (112 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0244
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0262

theorem accepted0243 : B0243.accepted = true := by decide +kernel
theorem checked0243 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6700_6900.SplitData.node0243 (maskNeeds ![93536104789220322063437485742271932188681566159233, 618970019642691236961191426, 77919046967349146032132, 5846006549663894039735755165580962022322679603208, 2993155353602138320208187523989443222265480496644112, 182698855038962130087031371948671701637744951328, 2619010934119436665962303867217093532770167957225536]) := by
  rw [← treeEq0243]
  exact B0243.sound accepted0243
#print axioms checked0243

def Tip0229_0243 : Block := .tip HexagonCover.NBand.M6700_6900.SplitData.node0243 ![93536104789220322063437485742271932188681566159233, 618970019642691236961191426, 77919046967349146032132, 5846006549663894039735755165580962022322679603208, 2993155353602138320208187523989443222265480496644112, 182698855038962130087031371948671701637744951328, 2619010934119436665962303867217093532770167957225536] checked0243
def B0264 : Block := .branch 174 ![93536104789220322063436248406695556615721254388097, 1856910058928071511860315650, 77919046967349146032132, 5846006549663894039735755165580962022322679603208, 2993155353602138320208187523989443222265480496644112, 182698855038962130087031371948671701637744951328, 2619741684938102117096887155975024947496839902920768] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 727).pointIds 727), (.leaf 2 (Common.fact 711).pointIds 711), (.leaf 3 (Common.fact 719).pointIds 719), (.leaf 4 (Common.fact 717).pointIds 717), (.leaf 5 (Common.fact 709).pointIds 709), (.leaf 6 (Common.fact 716).pointIds 716)]
theorem treeEq0264 : B0264.tree = HexagonCover.NBand.M6700_6900.SplitData.node0264 := by
  change Tree.branch (174 : Fin 175) _ = Tree.branch (174 : Fin 175) _
  apply congrArg (Tree.branch (174 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0263 : Block := .branch 159 ![93536104789220322063436248406695556615721254388097, 1856910058928071511860315650, 77919046967349146032132, 5846006549663894039735755165580962022322679603208, 2993155353602138320208187523989443222265480496644112, 182698855038962130087031371948671701637744951328, 2619010934119436665637785313558666805987011936649280] ![(.leaf 0 (Common.fact 685).pointIds 685), (.leaf 1 (Common.fact 725).pointIds 725), (.leaf 2 (Common.fact 505).pointIds 505), (.leaf 3 (Common.fact 506).pointIds 506), (.leaf 4 (Common.fact 507).pointIds 507), (.leaf 5 (Common.fact 508).pointIds 508), B0264]
theorem treeEq0263 : B0263.tree = HexagonCover.NBand.M6700_6900.SplitData.node0263 := by
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
  · exact treeEq0264

def B0242 : Block := .branch 90 ![93536104789220322063436248406695556615721254388097, 618970019642691236961191426, 77919046967349146032132, 5846006549663894039735755165580962022322679603208, 2993155353602138320208187523989443222265480496644112, 182698855038962130087031371948671701637744951328, 2630702947218083889307933345878823796927415417569344] ![Tip0229_0243, B0263, (.leaf 2 (Common.fact 316).pointIds 316), (.leaf 3 (Common.fact 317).pointIds 317), (.leaf 4 (Common.fact 318).pointIds 318), (.leaf 5 (Common.fact 319).pointIds 319), (.leaf 6 (Common.fact 683).pointIds 683)]
theorem treeEq0242 : B0242.tree = HexagonCover.NBand.M6700_6900.SplitData.node0242 := by
  change Tree.branch (90 : Fin 175) _ = Tree.branch (90 : Fin 175) _
  apply congrArg (Tree.branch (90 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0263
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0266 : Block := .branch 174 ![93536104789220322063436247802822942618765372686721, 619574482552498551548544514, 77919046967349146032132, 5846006549663894039735755165580962022322679603208, 2993155353602138320208187523989443222265480496644112, 182698855038962130087031371948671701637744951328, 2619741684938102117096887155975024947496839902920768] ![(.leaf 0 (Common.fact 729).pointIds 729), (.leaf 1 (Common.fact 730).pointIds 730), (.leaf 2 (Common.fact 711).pointIds 711), (.leaf 3 (Common.fact 719).pointIds 719), (.leaf 4 (Common.fact 717).pointIds 717), (.leaf 5 (Common.fact 709).pointIds 709), (.leaf 6 (Common.fact 716).pointIds 716)]
theorem treeEq0266 : B0266.tree = HexagonCover.NBand.M6700_6900.SplitData.node0266 := by
  change Tree.branch (174 : Fin 175) _ = Tree.branch (174 : Fin 175) _
  apply congrArg (Tree.branch (174 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0265 : Block := .branch 159 ![93536104789220322063436247802822942618765372686721, 619574482552498551548544514, 77919046967349146032132, 5846006549663894039735755165580962022322679603208, 2993155353602138320208187523989443222265480496644112, 182698855038962130087031371948671701637744951328, 2619010934119436665637785313558666805987011936649280] ![(.leaf 0 (Common.fact 685).pointIds 685), (.leaf 1 (Common.fact 728).pointIds 728), (.leaf 2 (Common.fact 505).pointIds 505), (.leaf 3 (Common.fact 506).pointIds 506), (.leaf 4 (Common.fact 507).pointIds 507), (.leaf 5 (Common.fact 508).pointIds 508), B0266]
theorem treeEq0265 : B0265.tree = HexagonCover.NBand.M6700_6900.SplitData.node0265 := by
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
  · exact treeEq0266

def B0241 : Block := .branch 79 ![93536104789220322063436247802822942618765372686721, 618970019642691236961191426, 77919046967349146032132, 5846006549663894039735755165580962022322679603208, 2993155353602138320208187523989443222265480496644112, 182698855038962130087031371948671701637744951328, 2630702947218083889307933655363833618272484142350400] ![B0242, B0265, (.leaf 2 (Common.fact 305).pointIds 305), (.leaf 3 (Common.fact 306).pointIds 306), (.leaf 4 (Common.fact 307).pointIds 307), (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 682).pointIds 682)]
theorem treeEq0241 : B0241.tree = HexagonCover.NBand.M6700_6900.SplitData.node0241 := by
  change Tree.branch (79 : Fin 175) _ = Tree.branch (79 : Fin 175) _
  apply congrArg (Tree.branch (79 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0242
  · exact treeEq0265
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0268 : Block := .branch 174 ![93536104789220322063436247802232646808406667035009, 618970609938501595666843138, 77919046967349146032132, 5846006549663894039735755165580962022322679603208, 2993155353602138320208187523989443222265480496644112, 182698855038962130087031371948671701637744951328, 2619741684938102117096887155975024947496839902920768] ![(.leaf 0 (Common.fact 732).pointIds 732), (.leaf 1 (Common.fact 733).pointIds 733), (.leaf 2 (Common.fact 711).pointIds 711), (.leaf 3 (Common.fact 719).pointIds 719), (.leaf 4 (Common.fact 717).pointIds 717), (.leaf 5 (Common.fact 709).pointIds 709), (.leaf 6 (Common.fact 716).pointIds 716)]
theorem treeEq0268 : B0268.tree = HexagonCover.NBand.M6700_6900.SplitData.node0268 := by
  change Tree.branch (174 : Fin 175) _ = Tree.branch (174 : Fin 175) _
  apply congrArg (Tree.branch (174 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0267 : Block := .branch 159 ![93536104789220322063436247802232646808406667035009, 618970609938501595666843138, 77919046967349146032132, 5846006549663894039735755165580962022322679603208, 2993155353602138320208187523989443222265480496644112, 182698855038962130087031371948671701637744951328, 2619010934119436665637785313558666805987011936649280] ![(.leaf 0 (Common.fact 685).pointIds 685), (.leaf 1 (Common.fact 731).pointIds 731), (.leaf 2 (Common.fact 505).pointIds 505), (.leaf 3 (Common.fact 506).pointIds 506), (.leaf 4 (Common.fact 507).pointIds 507), (.leaf 5 (Common.fact 508).pointIds 508), B0268]
theorem treeEq0267 : B0267.tree = HexagonCover.NBand.M6700_6900.SplitData.node0267 := by
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
  · exact treeEq0268

def B0240 : Block := .branch 69 ![93536104789220322063436247802232646808406667035009, 618970019642691236961191426, 77919046967349146032132, 5846006549663894039735755165580962022322679603208, 2993155353602138320208187523989443222265480496644112, 182698855038962130087031371948671701637744951328, 2630702947218083889307933655363833618272484142350400] ![B0241, B0267, (.leaf 2 (Common.fact 478).pointIds 478), (.leaf 3 (Common.fact 479).pointIds 479), (.leaf 4 (Common.fact 480).pointIds 480), (.leaf 5 (Common.fact 481).pointIds 481), (.leaf 6 (Common.fact 681).pointIds 681)]
theorem treeEq0240 : B0240.tree = HexagonCover.NBand.M6700_6900.SplitData.node0240 := by
  change Tree.branch (69 : Fin 175) _ = Tree.branch (69 : Fin 175) _
  apply congrArg (Tree.branch (69 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0241
  · exact treeEq0267
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0239 : Block := .branch 138 ![93536104789220322063436247802232646808406667035009, 618970019642691236961191426, 77919046967349146032132, 5846006549663894039814983328095226359916223553544, 2993155353253689176481146537402947624255349848113168, 182698855038962130087031371948671701637744951328, 2630702947218083889307933655363833618272484142350400] ![(.leaf 0 (Common.fact 128).pointIds 128), (.leaf 1 (Common.fact 129).pointIds 129), (.leaf 2 (Common.fact 130).pointIds 130), (.leaf 3 (Common.fact 131).pointIds 131), B0240, (.leaf 5 (Common.fact 132).pointIds 132), (.leaf 6 (Common.fact 680).pointIds 680)]
theorem treeEq0239 : B0239.tree = HexagonCover.NBand.M6700_6900.SplitData.node0239 := by
  change Tree.branch (138 : Fin 175) _ = Tree.branch (138 : Fin 175) _
  apply congrArg (Tree.branch (138 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0240
  · rfl
  · rfl

def B0238 : Block := .branch 128 ![93536104789220322063436247802232646808406667035009, 618970019642691236961191426, 77919046967349146032132, 5846006549323611672894044864631851752484455342088, 2993155353253689176481146537402947624255349848113168, 182698855038962130087031371948671701637744951328, 2630702947218083889307933655363833618272484142350400] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), B0239, (.leaf 4 (Common.fact 678).pointIds 678), (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 679).pointIds 679)]
theorem treeEq0238 : B0238.tree = HexagonCover.NBand.M6700_6900.SplitData.node0238 := by
  change Tree.branch (128 : Fin 175) _ = Tree.branch (128 : Fin 175) _
  apply congrArg (Tree.branch (128 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0239
  · rfl
  · rfl
  · rfl

def B0237 : Block := .branch 129 ![93536104789220322063436247802232646808406667035009, 618970019642691236961191426, 77919046967349146032132, 5846006549323611672894044864631851752484455342088, 2993155353253689176481146537402947624255349848113168, 182698855038962130087031371948671701637744951328, 2630702947217403324574091778436906869057620605927488] ![(.leaf 0 (Common.fact 268).pointIds 268), (.leaf 1 (Common.fact 269).pointIds 269), (.leaf 2 (Common.fact 270).pointIds 270), (.leaf 3 (Common.fact 271).pointIds 271), (.leaf 4 (Common.fact 677).pointIds 677), (.leaf 5 (Common.fact 272).pointIds 272), B0238]
theorem treeEq0237 : B0237.tree = HexagonCover.NBand.M6700_6900.SplitData.node0237 := by
  change Tree.branch (129 : Fin 175) _ = Tree.branch (129 : Fin 175) _
  apply congrArg (Tree.branch (129 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0238

def B0236 : Block := .branch 125 ![93536104789177786767571130494299724982477696008577, 618970019642691236961191426, 77919046967349146032132, 5846006549323611672894044864631851752484455342088, 2993155353253689176481146537402947624255349848113168, 182698855038962130087031371948671701637744951328, 2630702947217403324574408691086963926407994781728832] ![B0237, (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), (.leaf 5 (Common.fact 676).pointIds 676), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq0236 : B0236.tree = HexagonCover.NBand.M6700_6900.SplitData.node0236 := by
  change Tree.branch (125 : Fin 175) _ = Tree.branch (125 : Fin 175) _
  apply congrArg (Tree.branch (125 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0237
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0235 : Block := .branch 118 ![93536104789177786767571130494299724982477696008577, 618970019642691236961191426, 77919046967349146032132, 5846006549323611672894044864631851752484455342088, 2993155353253689176481146537402947624255349848113168, 182698855038962130087031371948671701637744951328, 2630702947217403324574408691086963926407994781728832] ![(.leaf 0 (Common.fact 250).pointIds 250), (.leaf 1 (Common.fact 251).pointIds 251), (.leaf 2 (Common.fact 252).pointIds 252), B0236, (.leaf 4 (Common.fact 674).pointIds 674), (.leaf 5 (Common.fact 254).pointIds 254), (.leaf 6 (Common.fact 675).pointIds 675)]
theorem treeEq0235 : B0235.tree = HexagonCover.NBand.M6700_6900.SplitData.node0235 := by
  change Tree.branch (118 : Fin 175) _ = Tree.branch (118 : Fin 175) _
  apply congrArg (Tree.branch (118 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0236
  · rfl
  · rfl
  · rfl

def B0234 : Block := .branch 162 ![93536104789177786767571130494299724982477696008577, 618970019642691236961191426, 77919046967349146032132, 79305533766719673860725170184, 2993155353253689176481146537402947624255349848113168, 182698855038962130087031371948671701637744951328, 2630702947217403324574408691086963926407994781728832] ![(.leaf 0 (Common.fact 357).pointIds 357), (.leaf 1 (Common.fact 358).pointIds 358), (.leaf 2 (Common.fact 359).pointIds 359), B0235, (.leaf 4 (Common.fact 672).pointIds 672), (.leaf 5 (Common.fact 360).pointIds 360), (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq0234 : B0234.tree = HexagonCover.NBand.M6700_6900.SplitData.node0234 := by
  change Tree.branch (162 : Fin 175) _ = Tree.branch (162 : Fin 175) _
  apply congrArg (Tree.branch (162 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0235
  · rfl
  · rfl
  · rfl

def B0233 : Block := .branch 169 ![93536104789177786767571130494299724982477696008577, 618970019642691236961191426, 77919046967349146032132, 79305533766719673860725170184, 2993156066877535529461087066545932349002918039486480, 182698855038962130087031371948671701637744951328, 1882414108903981030454122056736227020344157319725120] ![(.leaf 0 (Common.fact 669).pointIds 669), (.leaf 1 (Common.fact 569).pointIds 569), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 627).pointIds 627), (.leaf 4 (Common.fact 670).pointIds 670), (.leaf 5 (Common.fact 671).pointIds 671), B0234]
theorem treeEq0233 : B0233.tree = HexagonCover.NBand.M6700_6900.SplitData.node0233 := by
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
  · exact treeEq0234

def B0232 : Block := .branch 143 ![93536104789177786767571130494299724982477696008577, 618970019642691236961191426, 77919046967349146032132, 79305533766719673860725170184, 2993156066877535529461087066545932349002918039486480, 182687704666362864775460604089535377456991961120, 1882414108903981030454122056736227020344157319725120] ![(.leaf 0 (Common.fact 601).pointIds 601), (.leaf 1 (Common.fact 602).pointIds 602), (.leaf 2 (Common.fact 603).pointIds 603), (.leaf 3 (Common.fact 604).pointIds 604), (.leaf 4 (Common.fact 667).pointIds 667), B0233, (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq0232 : B0232.tree = HexagonCover.NBand.M6700_6900.SplitData.node0232 := by
  change Tree.branch (143 : Fin 175) _ = Tree.branch (143 : Fin 175) _
  apply congrArg (Tree.branch (143 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0233
  · rfl

def B0231 : Block := .branch 166 ![2535301200457611724498013258113, 618970019642691236961191426, 77919046967349146032132, 79305533766719673860725170184, 2993156066877535529461087066545932349002918039486480, 185542200051774784537577176028434367729757454368, 1882414108903981030454122056736227020344157319725120] ![B0232, (.leaf 1 (Common.fact 216).pointIds 216), (.leaf 2 (Common.fact 217).pointIds 217), (.leaf 3 (Common.fact 218).pointIds 218), (.leaf 4 (Common.fact 219).pointIds 219), (.leaf 5 (Common.fact 665).pointIds 665), (.leaf 6 (Common.fact 666).pointIds 666)]
theorem treeEq0231 : B0231.tree = HexagonCover.NBand.M6700_6900.SplitData.node0231 := by
  change Tree.branch (166 : Fin 175) _ = Tree.branch (166 : Fin 175) _
  apply congrArg (Tree.branch (166 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0232
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0230 : Block := .branch 151 ![2535301200457611724498013258113, 618970019642691236961191426, 77919046967349146032132, 79305533766719673860725170184, 2993156066877535529461087066545932349002918039486480, 182687704666362864775460604089535377456991961120, 1882414108903981030454122056736227020344157319725120] ![(.leaf 0 (Common.fact 233).pointIds 233), (.leaf 1 (Common.fact 234).pointIds 234), (.leaf 2 (Common.fact 235).pointIds 235), (.leaf 3 (Common.fact 236).pointIds 236), (.leaf 4 (Common.fact 664).pointIds 664), B0231, (.leaf 6 (Common.fact 468).pointIds 468)]
theorem treeEq0230 : B0230.tree = HexagonCover.NBand.M6700_6900.SplitData.node0230 := by
  change Tree.branch (151 : Fin 175) _ = Tree.branch (151 : Fin 175) _
  apply congrArg (Tree.branch (151 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0231
  · rfl

def B0229 : Block := .branch 157 ![2535301200457611724498013258113, 618970019642691236961191426, 77919046967349146032132, 79305533766719673860725170184, 2993156066877535529461087066545932349002918039486480, 393248, 1882414108903981030454122056736227020344157319725120] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 663).pointIds 663), B0230, (.leaf 0 [] 0)]
theorem treeEq0229 : B0229.tree = HexagonCover.NBand.M6700_6900.SplitData.node0229 := by
  change Tree.branch (157 : Fin 175) _ = Tree.branch (157 : Fin 175) _
  apply congrArg (Tree.branch (157 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0230
  · rfl

theorem accepted0229 : B0229.accepted = true := by decide +kernel
theorem checked0229 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6700_6900.SplitData.node0229 (maskNeeds ![2535301200457611724498013258113, 618970019642691236961191426, 77919046967349146032132, 79305533766719673860725170184, 2993156066877535529461087066545932349002918039486480, 393248, 1882414108903981030454122056736227020344157319725120]) := by
  rw [← treeEq0229]
  exact B0229.sound accepted0229
#print axioms checked0229

def Tip0122_0128 : Block := .tip HexagonCover.NBand.M6700_6900.SplitData.node0128 ![10387129018270112868785490671698305, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 2854495385411919762116571938898990272765886496, 374144419189378254284870786545424204713895497564224] HexagonCover.NBand.M6700_6900.SplitTree.Run0001.checked0128
def Tip0122_0229 : Block := .tip HexagonCover.NBand.M6700_6900.SplitData.node0229 ![2535301200457611724498013258113, 618970019642691236961191426, 77919046967349146032132, 79305533766719673860725170184, 2993156066877535529461087066545932349002918039486480, 393248, 1882414108903981030454122056736227020344157319725120] checked0229
def B0127 : Block := .branch 133 ![10387129018270112868785490671698305, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 2854495385411919762116571938898990272765886496, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 471).pointIds 471), (.leaf 1 (Common.fact 472).pointIds 472), (.leaf 2 (Common.fact 473).pointIds 473), (.leaf 3 (Common.fact 474).pointIds 474), (.leaf 4 (Common.fact 475).pointIds 475), (.leaf 5 (Common.fact 476).pointIds 476), Tip0122_0128]
theorem treeEq0127 : B0127.tree = HexagonCover.NBand.M6700_6900.SplitData.node0127 := by
  change Tree.branch (133 : Fin 175) _ = Tree.branch (133 : Fin 175) _
  apply congrArg (Tree.branch (133 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0126 : Block := .branch 113 ![2535301200457611724498013258113, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 2854495385411919762116571938898990272765886496, 374144419178489218543400755714596217276078914797632] ![B0127, (.leaf 1 (Common.fact 332).pointIds 332), (.leaf 2 (Common.fact 333).pointIds 333), (.leaf 3 (Common.fact 334).pointIds 334), (.leaf 4 (Common.fact 335).pointIds 335), (.leaf 5 (Common.fact 469).pointIds 469), (.leaf 6 (Common.fact 470).pointIds 470)]
theorem treeEq0126 : B0126.tree = HexagonCover.NBand.M6700_6900.SplitData.node0126 := by
  change Tree.branch (113 : Fin 175) _ = Tree.branch (113 : Fin 175) _
  apply congrArg (Tree.branch (113 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0127
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0125 : Block := .branch 151 ![2535301200457611724498013258113, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 233).pointIds 233), (.leaf 1 (Common.fact 234).pointIds 234), (.leaf 2 (Common.fact 235).pointIds 235), (.leaf 3 (Common.fact 236).pointIds 236), (.leaf 4 (Common.fact 467).pointIds 467), B0126, (.leaf 6 (Common.fact 468).pointIds 468)]
theorem treeEq0125 : B0125.tree = HexagonCover.NBand.M6700_6900.SplitData.node0125 := by
  change Tree.branch (151 : Fin 175) _ = Tree.branch (151 : Fin 175) _
  apply congrArg (Tree.branch (151 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0126
  · rfl

def B0228 : Block := .branch 163 ![2535301200457611724498013258113, 618970019642691236961191426, 77919046967349146032132, 79305533766719673860725170184, 2993156066877535529461087066545932349002918039486480, 393248, 1870722095805333807108492578074496756186909859381312] ![(.leaf 0 (Common.fact 227).pointIds 227), (.leaf 1 (Common.fact 228).pointIds 228), (.leaf 2 (Common.fact 229).pointIds 229), (.leaf 3 (Common.fact 230).pointIds 230), (.leaf 4 (Common.fact 662).pointIds 662), (.leaf 5 (Common.fact 231).pointIds 231), Tip0122_0229]
theorem treeEq0228 : B0228.tree = HexagonCover.NBand.M6700_6900.SplitData.node0228 := by
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
  · rfl

def B0227 : Block := .branch 165 ![2535301200457611724498013258113, 618970019642691236961191426, 77919046967349146032132, 79305533766719673860725170184, 2993156066877535529461087066545932349002918039486480, 393248, 1870722095805333807108492578074496756186909859381312] ![(.leaf 0 (Common.fact 342).pointIds 342), (.leaf 1 (Common.fact 343).pointIds 343), (.leaf 2 (Common.fact 344).pointIds 344), (.leaf 3 (Common.fact 345).pointIds 345), (.leaf 4 (Common.fact 661).pointIds 661), B0228, (.leaf 0 [] 0)]
theorem treeEq0227 : B0227.tree = HexagonCover.NBand.M6700_6900.SplitData.node0227 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0228
  · rfl

def B0226 : Block := .branch 113 ![2535301200457611724498013258113, 618970019642691236961191426, 77919046967349146032132, 79305533766719673860725170184, 2993156066877535529461087066545932349002918039486480, 187072209578355573530071658587684226515959365894176, 1870722095805333807108492578074496756186909859381312] ![B0227, (.leaf 1 (Common.fact 332).pointIds 332), (.leaf 2 (Common.fact 333).pointIds 333), (.leaf 3 (Common.fact 334).pointIds 334), (.leaf 4 (Common.fact 335).pointIds 335), (.leaf 5 (Common.fact 340).pointIds 340), (.leaf 6 (Common.fact 470).pointIds 470)]
theorem treeEq0226 : B0226.tree = HexagonCover.NBand.M6700_6900.SplitData.node0226 := by
  change Tree.branch (113 : Fin 175) _ = Tree.branch (113 : Fin 175) _
  apply congrArg (Tree.branch (113 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0227
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0225 : Block := .branch 167 ![2535301200457611724498013258113, 618970019642691236961191426, 77919046967349146032132, 79305533766719673860725170184, 2993156066877535529461087066545932349002918039486480, 393248, 1870722095805333807108492578074496756186909859381312] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 339).pointIds 339), (.leaf 4 (Common.fact 660).pointIds 660), B0226, (.leaf 6 (Common.fact 341).pointIds 341)]
theorem treeEq0225 : B0225.tree = HexagonCover.NBand.M6700_6900.SplitData.node0225 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0226
  · rfl

def B0224 : Block := .branch 171 ![2535301200457611724498013258113, 618970019642691236961191426, 77919046967349146032132, 79305533766719673860725170184, 713623846352979940529142984724747568191471632, 393248, 1870722095805333807108492578074496756186909859381312] ![(.leaf 0 (Common.fact 657).pointIds 657), (.leaf 1 (Common.fact 566).pointIds 566), (.leaf 2 (Common.fact 544).pointIds 544), (.leaf 3 (Common.fact 597).pointIds 597), B0225, (.leaf 5 (Common.fact 658).pointIds 658), (.leaf 6 (Common.fact 659).pointIds 659)]
theorem treeEq0224 : B0224.tree = HexagonCover.NBand.M6700_6900.SplitData.node0224 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0225
  · rfl
  · rfl

def B0223 : Block := .branch 170 ![2535301200457611724498013258113, 618970019642691236961191426, 77919046967349146032132, 79305533766719673860725170184, 713623846352979940529142984724747568191471632, 393248, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 654).pointIds 654), (.leaf 1 (Common.fact 573).pointIds 573), (.leaf 2 (Common.fact 542).pointIds 542), (.leaf 3 (Common.fact 594).pointIds 594), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 656).pointIds 656), B0224]
theorem treeEq0223 : B0223.tree = HexagonCover.NBand.M6700_6900.SplitData.node0223 := by
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
  · exact treeEq0224

def B0124 : Block := .branch 108 ![2535301200457611724498013258113, 618970019642691236961191426, 77919046967349146032132, 79305533766719673860725170184, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 275).pointIds 275), (.leaf 1 (Common.fact 276).pointIds 276), (.leaf 2 (Common.fact 277).pointIds 277), (.leaf 3 (Common.fact 278).pointIds 278), B0125, (.leaf 5 (Common.fact 279).pointIds 279), B0223]
theorem treeEq0124 : B0124.tree = HexagonCover.NBand.M6700_6900.SplitData.node0124 := by
  change Tree.branch (108 : Fin 175) _ = Tree.branch (108 : Fin 175) _
  apply congrArg (Tree.branch (108 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0125
  · rfl
  · exact treeEq0223

def B0270 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 374144419178489218545935747430042854734003596427328] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), (.leaf 4 (Common.fact 735).pointIds 735), (.leaf 5 (Common.fact 156).pointIds 156), (.leaf 6 (Common.fact 736).pointIds 736)]
theorem treeEq0270 : B0270.tree = HexagonCover.NBand.M6700_6900.SplitData.node0270 := by
  change Tree.branch (132 : Fin 175) _ = Tree.branch (132 : Fin 175) _
  apply congrArg (Tree.branch (132 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0269 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 374144419178489218545935747430042854734003596427328] ![(.leaf 0 (Common.fact 227).pointIds 227), (.leaf 1 (Common.fact 228).pointIds 228), (.leaf 2 (Common.fact 229).pointIds 229), (.leaf 3 (Common.fact 230).pointIds 230), B0270, (.leaf 5 (Common.fact 231).pointIds 231), (.leaf 6 (Common.fact 734).pointIds 734)]
theorem treeEq0269 : B0269.tree = HexagonCover.NBand.M6700_6900.SplitData.node0269 := by
  change Tree.branch (163 : Fin 175) _ = Tree.branch (163 : Fin 175) _
  apply congrArg (Tree.branch (163 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0270
  · rfl
  · rfl

def B0123 : Block := .branch 101 ![1152921504606847361, 618970019642691236961191426, 77919046967349146032132, 79305533766719673860725170184, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![B0124, (.leaf 1 (Common.fact 222).pointIds 222), (.leaf 2 (Common.fact 223).pointIds 223), (.leaf 3 (Common.fact 224).pointIds 224), (.leaf 4 (Common.fact 225).pointIds 225), (.leaf 5 (Common.fact 226).pointIds 226), B0269]
theorem treeEq0123 : B0123.tree = HexagonCover.NBand.M6700_6900.SplitData.node0123 := by
  change Tree.branch (101 : Fin 175) _ = Tree.branch (101 : Fin 175) _
  apply congrArg (Tree.branch (101 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0124
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0269

def B0272 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 374144419178489218543402922109664966691559988265024] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), (.leaf 4 (Common.fact 735).pointIds 735), (.leaf 5 (Common.fact 156).pointIds 156), (.leaf 6 (Common.fact 738).pointIds 738)]
theorem treeEq0272 : B0272.tree = HexagonCover.NBand.M6700_6900.SplitData.node0272 := by
  change Tree.branch (132 : Fin 175) _ = Tree.branch (132 : Fin 175) _
  apply congrArg (Tree.branch (132 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0271 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 374144419178489218543402922109664966691559988265024] ![(.leaf 0 (Common.fact 227).pointIds 227), (.leaf 1 (Common.fact 228).pointIds 228), (.leaf 2 (Common.fact 229).pointIds 229), (.leaf 3 (Common.fact 230).pointIds 230), B0272, (.leaf 5 (Common.fact 231).pointIds 231), (.leaf 6 (Common.fact 737).pointIds 737)]
theorem treeEq0271 : B0271.tree = HexagonCover.NBand.M6700_6900.SplitData.node0271 := by
  change Tree.branch (163 : Fin 175) _ = Tree.branch (163 : Fin 175) _
  apply congrArg (Tree.branch (163 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0272
  · rfl
  · rfl

def B0122 : Block := .branch 91 ![1152921504606847361, 618970019642691236961191426, 77919046967349146032132, 79305533766719673860725170184, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![B0123, (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 329).pointIds 329), (.leaf 5 (Common.fact 330).pointIds 330), B0271]
theorem treeEq0122 : B0122.tree = HexagonCover.NBand.M6700_6900.SplitData.node0122 := by
  change Tree.branch (91 : Fin 175) _ = Tree.branch (91 : Fin 175) _
  apply congrArg (Tree.branch (91 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0123
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0271

theorem accepted0122 : B0122.accepted = true := by decide +kernel
theorem checked0122 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6700_6900.SplitData.node0122 (maskNeeds ![1152921504606847361, 618970019642691236961191426, 77919046967349146032132, 79305533766719673860725170184, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq0122]
  exact B0122.sound accepted0122
#print axioms checked0122

def B0291 : Block := .branch 121 ![385, 1538, 6148, 24584, 23945242828817106561665500191915545778123843972464656, 393248, 1894106122002628253475232594883268281036912853516352] ![(.leaf 0 (Common.fact 193).pointIds 193), (.leaf 1 (Common.fact 194).pointIds 194), (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 772).pointIds 772), (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 773).pointIds 773)]
theorem treeEq0291 : B0291.tree = HexagonCover.NBand.M6700_6900.SplitData.node0291 := by
  change Tree.branch (121 : Fin 175) _ = Tree.branch (121 : Fin 175) _
  apply congrArg (Tree.branch (121 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0290 : Block := .branch 174 ![21267647932558653967613834469092360577, 302231526962350843233794, 77919046967349146032132, 38685626227668133590622216, 2787593149816327892691964784081045188345872, 43556142965880123323311949751266331459616, 1894106122002628253475232594883268281036912853516352] ![(.leaf 0 (Common.fact 768).pointIds 768), (.leaf 1 (Common.fact 753).pointIds 753), (.leaf 2 (Common.fact 711).pointIds 711), (.leaf 3 (Common.fact 769).pointIds 769), B0291, (.leaf 5 (Common.fact 770).pointIds 770), (.leaf 6 (Common.fact 771).pointIds 771)]
theorem treeEq0290 : B0290.tree = HexagonCover.NBand.M6700_6900.SplitData.node0290 := by
  change Tree.branch (174 : Fin 175) _ = Tree.branch (174 : Fin 175) _
  apply congrArg (Tree.branch (174 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0291
  · rfl
  · rfl

def B0289 : Block := .branch 170 ![21267647932558653967613834469092360577, 302231526962350843233794, 77919046967349146032132, 38685626227668133590622216, 3832940580997450852451451578111437133938704, 43556142965880123323311949751266331459616, 397528445375783665234659326181794468909237929508928] ![(.leaf 0 (Common.fact 765).pointIds 765), (.leaf 1 (Common.fact 745).pointIds 745), (.leaf 2 (Common.fact 542).pointIds 542), (.leaf 3 (Common.fact 766).pointIds 766), (.leaf 4 (Common.fact 746).pointIds 746), (.leaf 5 (Common.fact 767).pointIds 767), B0290]
theorem treeEq0289 : B0289.tree = HexagonCover.NBand.M6700_6900.SplitData.node0289 := by
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
  · exact treeEq0290

def B0288 : Block := .branch 164 ![21267647932558653967613834469092360577, 302231526962350843233794, 77919046967349146032132, 38685626227668133590622216, 3832940580997450852451451578111437133938704, 43556142965880123323311949751266331459616, 374144419178489218543400368858333940594743008821312] ![(.leaf 0 (Common.fact 764).pointIds 764), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), B0289]
theorem treeEq0288 : B0288.tree = HexagonCover.NBand.M6700_6900.SplitData.node0288 := by
  change Tree.branch (164 : Fin 175) _ = Tree.branch (164 : Fin 175) _
  apply congrArg (Tree.branch (164 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0289

def B0287 : Block := .branch 124 ![1152921504606847361, 302231526962350843233794, 77919046967349146032132, 38685626227668133590622216, 3832940580997450852451451578111437133938704, 43556142965880123323311949751266331459616, 374144419178489218543400678343343761939811733602368] ![B0288, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 204).pointIds 204), (.leaf 6 (Common.fact 763).pointIds 763)]
theorem treeEq0287 : B0287.tree = HexagonCover.NBand.M6700_6900.SplitData.node0287 := by
  change Tree.branch (124 : Fin 175) _ = Tree.branch (124 : Fin 175) _
  apply congrArg (Tree.branch (124 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0288
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0286 : Block := .branch 135 ![1152921504606847361, 302231526962350843233794, 77919046967349146032132, 38685626227668133590622216, 3832940580997450852451451578111437133938704, 393248, 374144419178489218543400678343343761939811733602368] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), (.leaf 4 (Common.fact 150).pointIds 150), B0287, (.leaf 6 (Common.fact 762).pointIds 762)]
theorem treeEq0286 : B0286.tree = HexagonCover.NBand.M6700_6900.SplitData.node0286 := by
  change Tree.branch (135 : Fin 175) _ = Tree.branch (135 : Fin 175) _
  apply congrArg (Tree.branch (135 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0287
  · rfl

def B0285 : Block := .branch 138 ![1152921504606847361, 302231526962350843233794, 77919046967349146032132, 79266848140492005727134572552, 3484491437270409865864955980101306485407760, 393248, 374144419178489218543400678343343761939811733602368] ![(.leaf 0 (Common.fact 128).pointIds 128), (.leaf 1 (Common.fact 129).pointIds 129), (.leaf 2 (Common.fact 130).pointIds 130), (.leaf 3 (Common.fact 131).pointIds 131), B0286, (.leaf 5 (Common.fact 132).pointIds 132), (.leaf 6 (Common.fact 761).pointIds 761)]
theorem treeEq0285 : B0285.tree = HexagonCover.NBand.M6700_6900.SplitData.node0285 := by
  change Tree.branch (138 : Fin 175) _ = Tree.branch (138 : Fin 175) _
  apply congrArg (Tree.branch (138 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0286
  · rfl
  · rfl

def B0284 : Block := .branch 139 ![1152921504606847361, 302231526962350843233794, 77919046967349146032132, 79266848140492005727134572552, 2787593149816327892691964784081045188345872, 393248, 374144419178489218543400678343343761939811733602368] ![(.leaf 0 (Common.fact 122).pointIds 122), (.leaf 1 (Common.fact 123).pointIds 123), (.leaf 2 (Common.fact 124).pointIds 124), (.leaf 3 (Common.fact 125).pointIds 125), B0285, (.leaf 5 (Common.fact 126).pointIds 126), (.leaf 6 (Common.fact 760).pointIds 760)]
theorem treeEq0284 : B0284.tree = HexagonCover.NBand.M6700_6900.SplitData.node0284 := by
  change Tree.branch (139 : Fin 175) _ = Tree.branch (139 : Fin 175) _
  apply congrArg (Tree.branch (139 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0285
  · rfl
  · rfl

def B0283 : Block := .branch 140 ![1152921504606847361, 302231526962350843233794, 77919046967349146032132, 79266848140492005727134572552, 2787593149816327892691964784081045188345872, 393248, 374144419178489218543400678343343761939811733602368] ![(.leaf 0 (Common.fact 116).pointIds 116), (.leaf 1 (Common.fact 117).pointIds 117), (.leaf 2 (Common.fact 118).pointIds 118), (.leaf 3 (Common.fact 119).pointIds 119), B0284, (.leaf 5 (Common.fact 120).pointIds 120), (.leaf 6 (Common.fact 759).pointIds 759)]
theorem treeEq0283 : B0283.tree = HexagonCover.NBand.M6700_6900.SplitData.node0283 := by
  change Tree.branch (140 : Fin 175) _ = Tree.branch (140 : Fin 175) _
  apply congrArg (Tree.branch (140 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0284
  · rfl
  · rfl

def B0282 : Block := .branch 141 ![1152921504606847361, 302231526962350843233794, 77919046967349146032132, 79266848140492005727134572552, 98320, 393248, 374144419178489218543400678343343761939811733602368] ![(.leaf 0 (Common.fact 110).pointIds 110), (.leaf 1 (Common.fact 111).pointIds 111), (.leaf 2 (Common.fact 112).pointIds 112), (.leaf 3 (Common.fact 113).pointIds 113), B0283, (.leaf 5 (Common.fact 114).pointIds 114), (.leaf 6 (Common.fact 758).pointIds 758)]
theorem treeEq0282 : B0282.tree = HexagonCover.NBand.M6700_6900.SplitData.node0282 := by
  change Tree.branch (141 : Fin 175) _ = Tree.branch (141 : Fin 175) _
  apply congrArg (Tree.branch (141 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0283
  · rfl
  · rfl

def B0281 : Block := .branch 144 ![1152921504606847361, 302231526962350843233794, 77919046967349146032132, 79266848140492005727134572552, 98320, 393248, 374144419178489218543400678343343761939811733602368] ![(.leaf 0 (Common.fact 104).pointIds 104), (.leaf 1 (Common.fact 105).pointIds 105), (.leaf 2 (Common.fact 106).pointIds 106), (.leaf 3 (Common.fact 107).pointIds 107), (.leaf 4 (Common.fact 108).pointIds 108), B0282, (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq0281 : B0281.tree = HexagonCover.NBand.M6700_6900.SplitData.node0281 := by
  change Tree.branch (144 : Fin 175) _ = Tree.branch (144 : Fin 175) _
  apply congrArg (Tree.branch (144 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0282
  · rfl

theorem accepted0281 : B0281.accepted = true := by decide +kernel
theorem checked0281 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6700_6900.SplitData.node0281 (maskNeeds ![1152921504606847361, 302231526962350843233794, 77919046967349146032132, 79266848140492005727134572552, 98320, 393248, 374144419178489218543400678343343761939811733602368]) := by
  rw [← treeEq0281]
  exact B0281.sound accepted0281
#print axioms checked0281

def Tip0119_0122 : Block := .tip HexagonCover.NBand.M6700_6900.SplitData.node0122 ![1152921504606847361, 618970019642691236961191426, 77919046967349146032132, 79305533766719673860725170184, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] checked0122
def Tip0119_0281 : Block := .tip HexagonCover.NBand.M6700_6900.SplitData.node0281 ![1152921504606847361, 302231526962350843233794, 77919046967349146032132, 79266848140492005727134572552, 98320, 393248, 374144419178489218543400678343343761939811733602368] checked0281
def B0280 : Block := .branch 174 ![1208926972536133781553537, 302231526962350843233794, 77919046967349146032132, 77371252455336267181219848, 2993155353602138320208187523989443222265480496644112, 22300745198530623141535718272648361506373664, 374144419178489218543401065199606038621147639578688] ![(.leaf 0 (Common.fact 752).pointIds 752), (.leaf 1 (Common.fact 753).pointIds 753), (.leaf 2 (Common.fact 711).pointIds 711), (.leaf 3 (Common.fact 754).pointIds 754), (.leaf 4 (Common.fact 717).pointIds 717), (.leaf 5 (Common.fact 755).pointIds 755), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq0280 : B0280.tree = HexagonCover.NBand.M6700_6900.SplitData.node0280 := by
  change Tree.branch (174 : Fin 175) _ = Tree.branch (174 : Fin 175) _
  apply congrArg (Tree.branch (174 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0279 : Block := .branch 171 ![1208926972536133781553537, 302231526962350843233794, 77919046967349146032132, 77371252455336267181219848, 348449143727040986586495598010130648629264, 22300745198530623141535718272648361506373664, 374144419178489218543401065199606038621147639578688] ![(.leaf 0 (Common.fact 748).pointIds 748), (.leaf 1 (Common.fact 749).pointIds 749), (.leaf 2 (Common.fact 544).pointIds 544), (.leaf 3 (Common.fact 597).pointIds 597), B0280, (.leaf 5 (Common.fact 750).pointIds 750), (.leaf 6 (Common.fact 751).pointIds 751)]
theorem treeEq0279 : B0279.tree = HexagonCover.NBand.M6700_6900.SplitData.node0279 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0280
  · rfl
  · rfl

def B0278 : Block := .branch 170 ![1208926972536133781553537, 302231526962350843233794, 77919046967349146032132, 77371252455336267181219848, 3832940580997450852451451578111437133938704, 22300745198530623141535718272648361506373664, 374144419178489218543401065199606038621147639578688] ![(.leaf 0 (Common.fact 744).pointIds 744), (.leaf 1 (Common.fact 745).pointIds 745), (.leaf 2 (Common.fact 542).pointIds 542), (.leaf 3 (Common.fact 594).pointIds 594), (.leaf 4 (Common.fact 746).pointIds 746), (.leaf 5 (Common.fact 747).pointIds 747), B0279]
theorem treeEq0278 : B0278.tree = HexagonCover.NBand.M6700_6900.SplitData.node0278 := by
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
  · exact treeEq0279

def B0277 : Block := .branch 138 ![1208926972536133781553537, 302231526962350843233794, 77919046967349146032132, 79305533766719673860725170184, 3484491437270409865864955980101306485407760, 22300745198530623141535718272648361506373664, 374144419178489218543401065199606038621147639578688] ![(.leaf 0 (Common.fact 128).pointIds 128), (.leaf 1 (Common.fact 129).pointIds 129), (.leaf 2 (Common.fact 130).pointIds 130), (.leaf 3 (Common.fact 131).pointIds 131), B0278, (.leaf 5 (Common.fact 132).pointIds 132), (.leaf 6 (Common.fact 743).pointIds 743)]
theorem treeEq0277 : B0277.tree = HexagonCover.NBand.M6700_6900.SplitData.node0277 := by
  change Tree.branch (138 : Fin 175) _ = Tree.branch (138 : Fin 175) _
  apply congrArg (Tree.branch (138 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0278
  · rfl
  · rfl

def B0276 : Block := .branch 139 ![1208926972536133781553537, 302231526962350843233794, 77919046967349146032132, 79305533766719673860725170184, 2787593149816327892691964784081045188345872, 22300745198530623141535718272648361506373664, 374144419178489218543401065199606038621147639578688] ![(.leaf 0 (Common.fact 122).pointIds 122), (.leaf 1 (Common.fact 123).pointIds 123), (.leaf 2 (Common.fact 124).pointIds 124), (.leaf 3 (Common.fact 125).pointIds 125), B0277, (.leaf 5 (Common.fact 126).pointIds 126), (.leaf 6 (Common.fact 742).pointIds 742)]
theorem treeEq0276 : B0276.tree = HexagonCover.NBand.M6700_6900.SplitData.node0276 := by
  change Tree.branch (139 : Fin 175) _ = Tree.branch (139 : Fin 175) _
  apply congrArg (Tree.branch (139 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0277
  · rfl
  · rfl

def B0275 : Block := .branch 140 ![1208926972536133781553537, 302231526962350843233794, 77919046967349146032132, 79305533766719673860725170184, 2787593149816327892691964784081045188345872, 22300745198530623141535718272648361506373664, 374144419178489218543401065199606038621147639578688] ![(.leaf 0 (Common.fact 116).pointIds 116), (.leaf 1 (Common.fact 117).pointIds 117), (.leaf 2 (Common.fact 118).pointIds 118), (.leaf 3 (Common.fact 119).pointIds 119), B0276, (.leaf 5 (Common.fact 120).pointIds 120), (.leaf 6 (Common.fact 741).pointIds 741)]
theorem treeEq0275 : B0275.tree = HexagonCover.NBand.M6700_6900.SplitData.node0275 := by
  change Tree.branch (140 : Fin 175) _ = Tree.branch (140 : Fin 175) _
  apply congrArg (Tree.branch (140 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0276
  · rfl
  · rfl

def B0274 : Block := .branch 141 ![1208926972536133781553537, 302231526962350843233794, 77919046967349146032132, 79305533766719673860725170184, 98320, 22300745198530623141535718272648361506373664, 374144419178489218543401065199606038621147639578688] ![(.leaf 0 (Common.fact 110).pointIds 110), (.leaf 1 (Common.fact 111).pointIds 111), (.leaf 2 (Common.fact 112).pointIds 112), (.leaf 3 (Common.fact 113).pointIds 113), B0275, (.leaf 5 (Common.fact 114).pointIds 114), (.leaf 6 (Common.fact 740).pointIds 740)]
theorem treeEq0274 : B0274.tree = HexagonCover.NBand.M6700_6900.SplitData.node0274 := by
  change Tree.branch (141 : Fin 175) _ = Tree.branch (141 : Fin 175) _
  apply congrArg (Tree.branch (141 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0275
  · rfl
  · rfl

def B0273 : Block := .branch 144 ![1208926972536133781553537, 302231526962350843233794, 77919046967349146032132, 79305533766719673860725170184, 98320, 393248, 374144419178489218543401065199606038621147639578688] ![(.leaf 0 (Common.fact 104).pointIds 104), (.leaf 1 (Common.fact 105).pointIds 105), (.leaf 2 (Common.fact 106).pointIds 106), (.leaf 3 (Common.fact 107).pointIds 107), (.leaf 4 (Common.fact 108).pointIds 108), B0274, (.leaf 6 (Common.fact 739).pointIds 739)]
theorem treeEq0273 : B0273.tree = HexagonCover.NBand.M6700_6900.SplitData.node0273 := by
  change Tree.branch (144 : Fin 175) _ = Tree.branch (144 : Fin 175) _
  apply congrArg (Tree.branch (144 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0274
  · rfl

def B0121 : Block := .branch 89 ![1208926972536133781553537, 302231526962350843233794, 77919046967349146032132, 79305533766719673860725170184, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 98).pointIds 98), Tip0119_0122, (.leaf 2 (Common.fact 100).pointIds 100), (.leaf 3 (Common.fact 101).pointIds 101), (.leaf 4 (Common.fact 102).pointIds 102), (.leaf 5 (Common.fact 103).pointIds 103), B0273]
theorem treeEq0121 : B0121.tree = HexagonCover.NBand.M6700_6900.SplitData.node0121 := by
  change Tree.branch (89 : Fin 175) _ = Tree.branch (89 : Fin 175) _
  apply congrArg (Tree.branch (89 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0273

def B0120 : Block := .branch 86 ![1208926972536133781553537, 302231526962350843233794, 77919046967349146032132, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 310).pointIds 310), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), B0121, (.leaf 4 (Common.fact 313).pointIds 313), (.leaf 5 (Common.fact 314).pointIds 314), Tip0119_0281]
theorem treeEq0120 : B0120.tree = HexagonCover.NBand.M6700_6900.SplitData.node0120 := by
  change Tree.branch (86 : Fin 175) _ = Tree.branch (86 : Fin 175) _
  apply congrArg (Tree.branch (86 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0121
  · rfl
  · rfl
  · rfl

def B0293 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 374144419178489218543400446531817850834667483693120] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), (.leaf 4 (Common.fact 735).pointIds 735), (.leaf 5 (Common.fact 156).pointIds 156), (.leaf 6 (Common.fact 775).pointIds 775)]
theorem treeEq0293 : B0293.tree = HexagonCover.NBand.M6700_6900.SplitData.node0293 := by
  change Tree.branch (132 : Fin 175) _ = Tree.branch (132 : Fin 175) _
  apply congrArg (Tree.branch (132 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0292 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 374144419178489218543400446531817850834667483693120] ![(.leaf 0 (Common.fact 227).pointIds 227), (.leaf 1 (Common.fact 228).pointIds 228), (.leaf 2 (Common.fact 229).pointIds 229), (.leaf 3 (Common.fact 230).pointIds 230), B0293, (.leaf 5 (Common.fact 231).pointIds 231), (.leaf 6 (Common.fact 774).pointIds 774)]
theorem treeEq0292 : B0292.tree = HexagonCover.NBand.M6700_6900.SplitData.node0292 := by
  change Tree.branch (163 : Fin 175) _ = Tree.branch (163 : Fin 175) _
  apply congrArg (Tree.branch (163 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0293
  · rfl
  · rfl

def B0119 : Block := .branch 78 ![1208926972536133781553537, 72058693549557250, 77919046967349146032132, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 140).pointIds 140), B0120, (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), (.leaf 4 (Common.fact 144).pointIds 144), (.leaf 5 (Common.fact 145).pointIds 145), B0292]
theorem treeEq0119 : B0119.tree = HexagonCover.NBand.M6700_6900.SplitData.node0119 := by
  change Tree.branch (78 : Fin 175) _ = Tree.branch (78 : Fin 175) _
  apply congrArg (Tree.branch (78 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0120
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0292

theorem accepted0119 : B0119.accepted = true := by decide +kernel
theorem checked0119 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6700_6900.SplitData.node0119 (maskNeeds ![1208926972536133781553537, 72058693549557250, 77919046967349146032132, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq0119]
  exact B0119.sound accepted0119
#print axioms checked0119

end HexagonCover.NBand.M6700_6900.SplitTree.Run0002
