import HexagonCover.NBand.M6900_7100.SplitData
import HexagonCover.NBand.M6900_7100.SplitTree.Run0032
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6900_7100.SplitTree.Run0033
open OwnerTree HexagonCover.NBand.M6900_7100

abbrev Block := Chunk (n := 173) (Certificate := Fin 1199) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip0076_2132 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2132 ![385, 148510702411681105410, 4777742743887792838660, 79266850501675247161957179400, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] HexagonCover.NBand.M6900_7100.SplitTree.Run0032.checked2132
def Tip0076_0118 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node0118 ![385, 148510702411681105410, 2416559502452970231812, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] HexagonCover.NBand.M6900_7100.SplitTree.Run0032.checked0118
def Tip0076_2434 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2434 ![748288838313422294120286634350736906063837462004097, 1099511629314, 6148, 79228162514264337593543974920, 98320, 42535295865117307932921825928971419680, 21778071483257438539264657732307602899008] HexagonCover.NBand.M6900_7100.SplitTree.Run0032.checked2434
def Tip0076_0077 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node0077 ![576460752303423873, 360289069701268994, 6148, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] HexagonCover.NBand.M6900_7100.SplitTree.Run0032.checked0077
def B2428 : Block := .branch 169 ![2993155353253689176481146537402947624255349848015233, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 5998002719627803647790863079356796219561733164367936] ![(.leaf 0 (Common.fact 928).pointIds 928), (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 1018).pointIds 1018)]
theorem treeEq2428 : B2428.tree = HexagonCover.NBand.M6900_7100.SplitData.node2428 := by
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

def B2427 : Block := .branch 171 ![385, 148510702411681105410, 55376261018147624964, 38692709777392438058442760, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 5998002719627803647790863079356796219561733164367936] ![B2428, (.leaf 1 (Common.fact 954).pointIds 954), (.leaf 2 (Common.fact 1025).pointIds 1025), (.leaf 3 (Common.fact 1026).pointIds 1026), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1017).pointIds 1017)]
theorem treeEq2427 : B2427.tree = HexagonCover.NBand.M6900_7100.SplitData.node2427 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2428
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2426 : Block := .branch 163 ![385, 148510702411681105410, 55376261018147624964, 38692709777392438058442760, 1496578395825877240853169583228388105037333491974160, 2854495385411919762116571938898990272765886496, 5986310706529156424445233600695065955404485704024128] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), (.leaf 4 (Common.fact 734).pointIds 734), (.leaf 5 (Common.fact 262).pointIds 262), B2427]
theorem treeEq2426 : B2426.tree = HexagonCover.NBand.M6900_7100.SplitData.node2426 := by
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
  · exact treeEq2427

def B2425 : Block := .branch 165 ![385, 148510702411681105410, 55376261018147624964, 38692709777392438058442760, 1496578395825877240853169583228388105037333491974160, 2854495385411919762116571938898990272765886496, 5986310706529156424445233600695065955404485704024128] ![(.leaf 0 (Common.fact 355).pointIds 355), (.leaf 1 (Common.fact 356).pointIds 356), (.leaf 2 (Common.fact 357).pointIds 357), (.leaf 3 (Common.fact 358).pointIds 358), (.leaf 4 (Common.fact 733).pointIds 733), B2426, (.leaf 0 [] 0)]
theorem treeEq2425 : B2425.tree = HexagonCover.NBand.M6900_7100.SplitData.node2425 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2426
  · rfl

def B2424 : Block := .branch 167 ![385, 148510702411681105410, 55376261018147624964, 38692709777392438058442760, 1496578395825877240853169583228388105037333491974160, 2854495385411919762116571938898990272765886496, 5986310706529156424445233600695065955404485704024128] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 732).pointIds 732), B2425, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq2424 : B2424.tree = HexagonCover.NBand.M6900_7100.SplitData.node2424 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2425
  · rfl

def B2423 : Block := .branch 142 ![385, 148510702411681105410, 55376261018147624964, 38692709777392438058442760, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 5986310706529156424445233600695065955404485704024128] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), B2424, (.leaf 5 (Common.fact 156).pointIds 156), (.leaf 6 (Common.fact 1014).pointIds 1014)]
theorem treeEq2423 : B2423.tree = HexagonCover.NBand.M6900_7100.SplitData.node2423 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2424
  · rfl
  · rfl

def B2422 : Block := .branch 151 ![385, 148510702411681105410, 55376261018147624964, 38692709777392438058442760, 1496578390250690941220513797844458536875243115479056, 393248, 5986310706529156424445233600695065955404485704024128] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B2423, (.leaf 6 (Common.fact 1013).pointIds 1013)]
theorem treeEq2422 : B2422.tree = HexagonCover.NBand.M6900_7100.SplitData.node2422 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2423
  · rfl

def B2421 : Block := .branch 170 ![385, 148510702411681105410, 55376261018147624964, 38692709777392438058442760, 713623846352979940529142984724747568191471632, 393248, 5986310706529156424445233600695065955404485704024128] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 838).pointIds 838), (.leaf 2 (Common.fact 839).pointIds 839), (.leaf 3 (Common.fact 840).pointIds 840), B2422, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 1012).pointIds 1012)]
theorem treeEq2421 : B2421.tree = HexagonCover.NBand.M6900_7100.SplitData.node2421 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2422
  · rfl
  · rfl

def B2420 : Block := .branch 172 ![385, 148510702411681105410, 55376261018147624964, 38692709777392438058442760, 713623846352979940529142984724747568191471632, 393248, 21778071482940525889170706893786007994432] ![(.leaf 0 (Common.fact 1009).pointIds 1009), (.leaf 1 (Common.fact 944).pointIds 944), (.leaf 2 (Common.fact 1023).pointIds 1023), (.leaf 3 (Common.fact 1024).pointIds 1024), (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), B2421]
theorem treeEq2420 : B2420.tree = HexagonCover.NBand.M6900_7100.SplitData.node2420 := by
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
  · exact treeEq2421

def B2131 : Block := .branch 72 ![385, 148510702411681105410, 55376261018147624964, 79266850501675247161957179400, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 421).pointIds 421), (.leaf 1 (Common.fact 422).pointIds 422), Tip0076_2132, B2420, (.leaf 4 (Common.fact 423).pointIds 423), (.leaf 5 (Common.fact 424).pointIds 424), (.leaf 6 (Common.fact 425).pointIds 425)]
theorem treeEq2131 : B2131.tree = HexagonCover.NBand.M6900_7100.SplitData.node2131 := by
  change Tree.branch (72 : Fin 173) _ = Tree.branch (72 : Fin 173) _
  apply congrArg (Tree.branch (72 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2420
  · rfl
  · rfl
  · rfl

def B0117 : Block := .branch 71 ![385, 148510702411681105410, 55376261018147624964, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), Tip0076_0118, B2131, (.leaf 4 (Common.fact 338).pointIds 338), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 0 [] 0)]
theorem treeEq0117 : B0117.tree = HexagonCover.NBand.M6900_7100.SplitData.node0117 := by
  change Tree.branch (71 : Fin 173) _ = Tree.branch (71 : Fin 173) _
  apply congrArg (Tree.branch (71 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2131
  · rfl
  · rfl
  · rfl

def B2431 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 158).pointIds 158), (.leaf 1 (Common.fact 159).pointIds 159), (.leaf 2 (Common.fact 160).pointIds 160), (.leaf 3 (Common.fact 161).pointIds 161), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 163).pointIds 163), (.leaf 6 (Common.fact 1029).pointIds 1029)]
theorem treeEq2431 : B2431.tree = HexagonCover.NBand.M6900_7100.SplitData.node2431 := by
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

def B2430 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), B2431, (.leaf 5 (Common.fact 156).pointIds 156), (.leaf 6 (Common.fact 1028).pointIds 1028)]
theorem treeEq2430 : B2430.tree = HexagonCover.NBand.M6900_7100.SplitData.node2430 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2431
  · rfl
  · rfl

def B2429 : Block := .branch 144 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 110).pointIds 110), (.leaf 1 (Common.fact 111).pointIds 111), (.leaf 2 (Common.fact 112).pointIds 112), (.leaf 3 (Common.fact 113).pointIds 113), (.leaf 4 (Common.fact 114).pointIds 114), B2430, (.leaf 6 (Common.fact 1027).pointIds 1027)]
theorem treeEq2429 : B2429.tree = HexagonCover.NBand.M6900_7100.SplitData.node2429 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2430
  · rfl

def B0116 : Block := .branch 67 ![385, 936749822004692482, 55376261018147624964, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 439).pointIds 439), B0117, (.leaf 2 (Common.fact 440).pointIds 440), (.leaf 3 (Common.fact 441).pointIds 441), (.leaf 4 (Common.fact 442).pointIds 442), (.leaf 5 (Common.fact 443).pointIds 443), B2429]
theorem treeEq0116 : B0116.tree = HexagonCover.NBand.M6900_7100.SplitData.node0116 := by
  change Tree.branch (67 : Fin 173) _ = Tree.branch (67 : Fin 173) _
  apply congrArg (Tree.branch (67 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0117
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2429

def B2433 : Block := .branch 125 ![748288838313422294120286634350736906063837462004097, 1099511629314, 6148, 79228162514264337593543974920, 98320, 393248, 21778071483257438539264657732307602899008] ![(.leaf 0 (Common.fact 853).pointIds 853), (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), Tip0076_2434, (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq2433 : B2433.tree = HexagonCover.NBand.M6900_7100.SplitData.node2433 := by
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

def B2432 : Block := .branch 169 ![385, 936749822004692482, 18482772870728521732, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539264657732307602899008] ![B2433, (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 1030).pointIds 1030)]
theorem treeEq2432 : B2432.tree = HexagonCover.NBand.M6900_7100.SplitData.node2432 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2433
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0115 : Block := .branch 65 ![385, 936749822004692482, 18482772870728521732, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), B0116, (.leaf 3 (Common.fact 142).pointIds 142), (.leaf 4 (Common.fact 143).pointIds 143), (.leaf 5 (Common.fact 144).pointIds 144), B2432]
theorem treeEq0115 : B0115.tree = HexagonCover.NBand.M6900_7100.SplitData.node0115 := by
  change Tree.branch (65 : Fin 173) _ = Tree.branch (65 : Fin 173) _
  apply congrArg (Tree.branch (65 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0116
  · rfl
  · rfl
  · rfl
  · exact treeEq2432

def B0076 : Block := .branch 59 ![385, 360289069701268994, 18482772870728521732, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![Tip0076_0077, B0115, (.leaf 2 (Common.fact 378).pointIds 378), (.leaf 3 (Common.fact 379).pointIds 379), (.leaf 4 (Common.fact 380).pointIds 380), (.leaf 5 (Common.fact 381).pointIds 381), (.leaf 6 (Common.fact 382).pointIds 382)]
theorem treeEq0076 : B0076.tree = HexagonCover.NBand.M6900_7100.SplitData.node0076 := by
  change Tree.branch (59 : Fin 173) _ = Tree.branch (59 : Fin 173) _
  apply congrArg (Tree.branch (59 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0115
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0076 : B0076.accepted = true := by decide +kernel
theorem checked0076 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node0076 (maskNeeds ![385, 360289069701268994, 18482772870728521732, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0076]
  exact B0076.sound accepted0076
#print axioms checked0076

def B2475 : Block := .branch 161 ![385, 1538, 18518801667747485700, 5986310706507378352962293152177147703846966877249544, 98320, 393248, 374144424753675518176056541098525785438169291292736] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 1047).pointIds 1047), (.leaf 3 (Common.fact 1048).pointIds 1048), (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 723).pointIds 723)]
theorem treeEq2475 : B2475.tree = HexagonCover.NBand.M6900_7100.SplitData.node2475 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2474 : Block := .branch 172 ![385, 144257025075840514, 18518801667747485700, 77371252455336267181219848, 713623846352979940529142984724747568191471632, 393248, 374144424753675518176056541098525785438169291292736] ![(.leaf 0 (Common.fact 1009).pointIds 1009), (.leaf 1 (Common.fact 1044).pointIds 1044), (.leaf 2 (Common.fact 1045).pointIds 1045), B2475, (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), (.leaf 6 (Common.fact 1046).pointIds 1046)]
theorem treeEq2474 : B2474.tree = HexagonCover.NBand.M6900_7100.SplitData.node2474 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2475
  · rfl
  · rfl
  · rfl

def B2473 : Block := .branch 142 ![385, 144257025075840514, 18518801667747485700, 77371252455336267181219848, 713623846353304459082801411451530724212047888, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), (.leaf 4 (Common.fact 468).pointIds 468), (.leaf 5 (Common.fact 156).pointIds 156), B2474]
theorem treeEq2473 : B2473.tree = HexagonCover.NBand.M6900_7100.SplitData.node2473 := by
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
  · exact treeEq2474

def B2472 : Block := .branch 166 ![385, 144257025075840514, 18518801667747485700, 77371252455336267181219848, 713623846353304459082801411451530724212047888, 2854495385411919762116571938898990272765886496, 374144419178489218543400755714596217276078914797632] ![B2473, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq2472 : B2472.tree = HexagonCover.NBand.M6900_7100.SplitData.node2472 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2473
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2471 : Block := .branch 151 ![385, 144257025075840514, 18518801667747485700, 77371252455336267181219848, 713623846353304459082801411451530724212047888, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 465).pointIds 465), B2472, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq2471 : B2471.tree = HexagonCover.NBand.M6900_7100.SplitData.node2471 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2472
  · rfl

def B2484 : Block := .branch 161 ![385, 1538, 18518801667747485700, 5986310706507378352962293152177147703846966877249544, 98320, 393248, 1870722095805333807108175665424439698836535683579968] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 1047).pointIds 1047), (.leaf 3 (Common.fact 1048).pointIds 1048), (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 1058).pointIds 1058)]
theorem treeEq2484 : B2484.tree = HexagonCover.NBand.M6900_7100.SplitData.node2484 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2483 : Block := .branch 172 ![385, 144257025075840514, 18518801667747485700, 77371252455336267181219848, 713623846352979940529142984724747568191471632, 393248, 1870722095805333807108175665424439698836535683579968] ![(.leaf 0 (Common.fact 1009).pointIds 1009), (.leaf 1 (Common.fact 1044).pointIds 1044), (.leaf 2 (Common.fact 1045).pointIds 1045), B2484, (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), (.leaf 6 (Common.fact 1057).pointIds 1057)]
theorem treeEq2483 : B2483.tree = HexagonCover.NBand.M6900_7100.SplitData.node2483 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2484
  · rfl
  · rfl
  · rfl

def B2482 : Block := .branch 170 ![385, 144257025075840514, 18518801667747485700, 116056878683004400771817480, 186255823898127764478106319013159115297948532752, 393248, 374144419178489218867602396722965886708860759572544] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1055).pointIds 1055), (.leaf 2 (Common.fact 1056).pointIds 1056), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 841).pointIds 841), (.leaf 5 (Common.fact 660).pointIds 660), B2483]
theorem treeEq2482 : B2482.tree = HexagonCover.NBand.M6900_7100.SplitData.node2482 := by
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
  · exact treeEq2483

def B2481 : Block := .branch 151 ![385, 144257025075840514, 18518801667747485700, 116056878683004400771817480, 183401328512715844715989747074260125025183039504, 2993155353253689176481146537402947624255349848408096, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), B2482, (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq2481 : B2481.tree = HexagonCover.NBand.M6900_7100.SplitData.node2481 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2482
  · rfl
  · rfl

def B2480 : Block := .branch 132 ![385, 144257025075840514, 18518801667747485700, 116056878683004400771817480, 183401328512715844715989747074260125025183039504, 2993155353253689176481146537402947624255349848408096, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 996).pointIds 996), (.leaf 5 (Common.fact 221).pointIds 221), B2481]
theorem treeEq2480 : B2480.tree = HexagonCover.NBand.M6900_7100.SplitData.node2480 := by
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
  · exact treeEq2481

def B2479 : Block := .branch 133 ![385, 144257025075840514, 18518801667747485700, 116056878683004400771817480, 183401328512715844715989747074260125025183039504, 2993155353253689176481146537402947624255349848408096, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 210).pointIds 210), (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), (.leaf 4 (Common.fact 995).pointIds 995), (.leaf 5 (Common.fact 215).pointIds 215), B2480]
theorem treeEq2479 : B2479.tree = HexagonCover.NBand.M6900_7100.SplitData.node2479 := by
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
  · exact treeEq2480

def B2478 : Block := .branch 157 ![385, 144257025075840514, 18518801667747485700, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 2993155353253689176481146537402947624255349848408096, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 205).pointIds 205), (.leaf 1 (Common.fact 206).pointIds 206), (.leaf 2 (Common.fact 207).pointIds 207), (.leaf 3 (Common.fact 208).pointIds 208), B2479, (.leaf 5 (Common.fact 994).pointIds 994), (.leaf 0 [] 0)]
theorem treeEq2478 : B2478.tree = HexagonCover.NBand.M6900_7100.SplitData.node2478 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2479
  · rfl
  · rfl

def B2477 : Block := .branch 171 ![748288838313422304507415652620848621927823526855041, 144257025075840514, 18518801667747485700, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 830).pointIds 830), (.leaf 1 (Common.fact 1051).pointIds 1051), (.leaf 2 (Common.fact 1052).pointIds 1052), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), B2478, (.leaf 6 (Common.fact 1054).pointIds 1054)]
theorem treeEq2477 : B2477.tree = HexagonCover.NBand.M6900_7100.SplitData.node2477 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2478
  · rfl

def B2476 : Block := .branch 169 ![10387129018270111715863986064851329, 618970019786947162525402626, 18518801667747485700, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 374144419178489218867919309373022944059234935373888] ![B2477, (.leaf 1 (Common.fact 1049).pointIds 1049), (.leaf 2 (Common.fact 1050).pointIds 1050), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 489).pointIds 489)]
theorem treeEq2476 : B2476.tree = HexagonCover.NBand.M6900_7100.SplitData.node2476 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2477
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2470 : Block := .branch 108 ![10387129018270111715863986064851329, 618970019786947162525402626, 18518801667747485700, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 318).pointIds 318), (.leaf 1 (Common.fact 319).pointIds 319), (.leaf 2 (Common.fact 320).pointIds 320), (.leaf 3 (Common.fact 321).pointIds 321), B2471, (.leaf 5 (Common.fact 322).pointIds 322), B2476]
theorem treeEq2470 : B2470.tree = HexagonCover.NBand.M6900_7100.SplitData.node2470 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2471
  · rfl
  · exact treeEq2476

theorem accepted2470 : B2470.accepted = true := by decide +kernel
theorem checked2470 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node2470 (maskNeeds ![10387129018270111715863986064851329, 618970019786947162525402626, 18518801667747485700, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq2470]
  exact B2470.sound accepted2470
#print axioms checked2470

def Tip2468_2470 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2470 ![10387129018270111715863986064851329, 618970019786947162525402626, 18518801667747485700, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] checked2470
def B2492 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 374144419178489218545935747430042854734003596427328] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 604).pointIds 604), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 605).pointIds 605)]
theorem treeEq2492 : B2492.tree = HexagonCover.NBand.M6900_7100.SplitData.node2492 := by
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

def B2491 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 374144419178489218545935747430042854734003596427328] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), B2492, (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 603).pointIds 603)]
theorem treeEq2491 : B2491.tree = HexagonCover.NBand.M6900_7100.SplitData.node2491 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2492
  · rfl
  · rfl

def B2490 : Block := .branch 166 ![385, 1538, 6148, 24584, 98320, 2854495385411919762116571938898990272765886496, 374144419178489218545936056915052676079072321208384] ![B2491, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq2490 : B2490.tree = HexagonCover.NBand.M6900_7100.SplitData.node2490 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2491
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2489 : Block := .branch 164 ![2993155353253689176481149013283026195015899646263681, 1538, 6148, 24584, 98320, 2854495385411919762116571938898990272765886496, 374144419178489218545936056915052676079072321208384] ![(.leaf 0 (Common.fact 1060).pointIds 1060), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), B2490]
theorem treeEq2489 : B2489.tree = HexagonCover.NBand.M6900_7100.SplitData.node2489 := by
  change Tree.branch (164 : Fin 173) _ = Tree.branch (164 : Fin 173) _
  apply congrArg (Tree.branch (164 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2490

def B2488 : Block := .branch 169 ![2993155353253689176481149013283026195015899646263681, 618970019642691236961191426, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 374144419178489218545936056915052676079072321208384] ![(.leaf 0 (Common.fact 1001).pointIds 1001), (.leaf 1 (Common.fact 1049).pointIds 1049), (.leaf 2 (Common.fact 1050).pointIds 1050), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), B2489]
theorem treeEq2488 : B2488.tree = HexagonCover.NBand.M6900_7100.SplitData.node2488 := by
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
  · exact treeEq2489

def B2487 : Block := .branch 171 ![2475880078570760549798248833, 618970019786947162525402626, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 374144419178489218545936056915052676079072321208384] ![B2488, (.leaf 1 (Common.fact 1051).pointIds 1051), (.leaf 2 (Common.fact 1052).pointIds 1052), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1059).pointIds 1059)]
theorem treeEq2487 : B2487.tree = HexagonCover.NBand.M6900_7100.SplitData.node2487 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2488
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2486 : Block := .branch 151 ![2475880078570760549798248833, 618970019786947162525402626, 18518801667747485700, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218545936056915052676079072321208384] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B2487, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq2486 : B2486.tree = HexagonCover.NBand.M6900_7100.SplitData.node2486 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2487
  · rfl

def B2485 : Block := .branch 170 ![2475880078570760549798248833, 618970019786947162525402626, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218545936056915052676079072321208384] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1055).pointIds 1055), (.leaf 2 (Common.fact 1056).pointIds 1056), (.leaf 3 (Common.fact 658).pointIds 658), B2486, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 729).pointIds 729)]
theorem treeEq2485 : B2485.tree = HexagonCover.NBand.M6900_7100.SplitData.node2485 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2486
  · rfl
  · rfl

def B2469 : Block := .branch 101 ![10384596192949733827821542456689025, 618970019786947162525402626, 18518801667747485700, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![Tip2468_2470, (.leaf 1 (Common.fact 460).pointIds 460), (.leaf 2 (Common.fact 461).pointIds 461), (.leaf 3 (Common.fact 462).pointIds 462), (.leaf 4 (Common.fact 463).pointIds 463), (.leaf 5 (Common.fact 464).pointIds 464), B2485]
theorem treeEq2469 : B2469.tree = HexagonCover.NBand.M6900_7100.SplitData.node2469 := by
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
  · exact treeEq2485

def B2494 : Block := .branch 161 ![385, 1538, 18518801667747485700, 5986310706507378352962293152177147703846966877249544, 98320, 393248, 374144419178489218543402922109664966691559988265024] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 1047).pointIds 1047), (.leaf 3 (Common.fact 1048).pointIds 1048), (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 1062).pointIds 1062)]
theorem treeEq2494 : B2494.tree = HexagonCover.NBand.M6900_7100.SplitData.node2494 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2493 : Block := .branch 172 ![385, 144257025075840514, 18518801667747485700, 77371252455336267181219848, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543402922109664966691559988265024] ![(.leaf 0 (Common.fact 1009).pointIds 1009), (.leaf 1 (Common.fact 1044).pointIds 1044), (.leaf 2 (Common.fact 1045).pointIds 1045), B2494, (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), (.leaf 6 (Common.fact 1061).pointIds 1061)]
theorem treeEq2493 : B2493.tree = HexagonCover.NBand.M6900_7100.SplitData.node2493 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2494
  · rfl
  · rfl
  · rfl

def B2468 : Block := .branch 91 ![10384593717069655257060992658440577, 618970019786947162525402626, 18518801667747485700, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![B2469, (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), (.leaf 3 (Common.fact 333).pointIds 333), (.leaf 4 (Common.fact 334).pointIds 334), (.leaf 5 (Common.fact 335).pointIds 335), B2493]
theorem treeEq2468 : B2468.tree = HexagonCover.NBand.M6900_7100.SplitData.node2468 := by
  change Tree.branch (91 : Fin 173) _ = Tree.branch (91 : Fin 173) _
  apply congrArg (Tree.branch (91 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2469
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2493

theorem accepted2468 : B2468.accepted = true := by decide +kernel
theorem checked2468 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node2468 (maskNeeds ![10384593717069655257060992658440577, 618970019786947162525402626, 18518801667747485700, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq2468]
  exact B2468.sound accepted2468
#print axioms checked2468

def B2514 : Block := .branch 69 ![2993155353253689176481146537402947624255349848015233, 748288838313422294120286634652968361109331755664898, 6148, 24584, 98320, 393248, 385836432277136441888713244355016968746685018144832] ![(.leaf 0 (Common.fact 1073).pointIds 1073), (.leaf 1 (Common.fact 1074).pointIds 1074), (.leaf 2 (Common.fact 491).pointIds 491), (.leaf 3 (Common.fact 492).pointIds 492), (.leaf 4 (Common.fact 493).pointIds 493), (.leaf 5 (Common.fact 494).pointIds 494), (.leaf 6 (Common.fact 1075).pointIds 1075)]
theorem treeEq2514 : B2514.tree = HexagonCover.NBand.M6900_7100.SplitData.node2514 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2513 : Block := .branch 169 ![2993155353253689176481146537402947624255349848015233, 302231455045494293661186, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 385836432277136441888713244355016968746685018144832] ![(.leaf 0 (Common.fact 928).pointIds 928), B2514, (.leaf 2 (Common.fact 1050).pointIds 1050), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 639).pointIds 639)]
theorem treeEq2513 : B2513.tree = HexagonCover.NBand.M6900_7100.SplitData.node2513 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2514
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2512 : Block := .branch 163 ![2993155353253689176481146537402947624255349848015233, 302231455045494293661186, 18518801667747485700, 38685626227668133590622216, 1496578395825877240853169583228388105037333491974160, 393248, 374144419178489218543083765693286704589437557801024] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), (.leaf 4 (Common.fact 734).pointIds 734), (.leaf 5 (Common.fact 262).pointIds 262), B2513]
theorem treeEq2512 : B2512.tree = HexagonCover.NBand.M6900_7100.SplitData.node2512 := by
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
  · exact treeEq2513

def B2511 : Block := .branch 165 ![2993155353253689176481146537402947624255349848015233, 302231455045494293661186, 18518801667747485700, 38685626227668133590622216, 1496578395825877240853169583228388105037333491974160, 393248, 374144419178489218543083765693286704589437557801024] ![(.leaf 0 (Common.fact 355).pointIds 355), (.leaf 1 (Common.fact 356).pointIds 356), (.leaf 2 (Common.fact 357).pointIds 357), (.leaf 3 (Common.fact 358).pointIds 358), (.leaf 4 (Common.fact 733).pointIds 733), B2512, (.leaf 0 [] 0)]
theorem treeEq2511 : B2511.tree = HexagonCover.NBand.M6900_7100.SplitData.node2511 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2512
  · rfl

def B2510 : Block := .branch 167 ![2993155353253689176481146537402947624255349848015233, 302231455045494293661186, 18518801667747485700, 38685626227668133590622216, 1496578395825877240853169583228388105037333491974160, 393248, 374144419178489218543083765693286704589437557801024] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 732).pointIds 732), B2511, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq2510 : B2510.tree = HexagonCover.NBand.M6900_7100.SplitData.node2510 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2511
  · rfl

def B2509 : Block := .branch 142 ![2993155353253689176481146537402947624255349848015233, 302231455045494293661186, 18518801667747485700, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400678343343761939811733602368] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), B2510, (.leaf 5 (Common.fact 156).pointIds 156), (.leaf 6 (Common.fact 638).pointIds 638)]
theorem treeEq2509 : B2509.tree = HexagonCover.NBand.M6900_7100.SplitData.node2509 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2510
  · rfl
  · rfl

def B2508 : Block := .branch 124 ![2993155353253689176481146537402947624255349848015233, 302231455045494293661186, 18518801667747485700, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 397528445375783665234659635666804290254306654289984] ![B2509, (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), (.leaf 6 (Common.fact 1072).pointIds 1072)]
theorem treeEq2508 : B2508.tree = HexagonCover.NBand.M6900_7100.SplitData.node2508 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2509
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2507 : Block := .branch 164 ![2993155353253689176481146537402947624255349848015233, 302231455045494293661186, 18518801667747485700, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400678343343761939811733602368] ![(.leaf 0 (Common.fact 1064).pointIds 1064), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), B2508]
theorem treeEq2507 : B2507.tree = HexagonCover.NBand.M6900_7100.SplitData.node2507 := by
  change Tree.branch (164 : Fin 173) _ = Tree.branch (164 : Fin 173) _
  apply congrArg (Tree.branch (164 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2508

def B2506 : Block := .branch 171 ![385, 302231599160682369517058, 18518801667747485700, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543400678343343761939811733602368] ![B2507, (.leaf 1 (Common.fact 1051).pointIds 1051), (.leaf 2 (Common.fact 1052).pointIds 1052), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1071).pointIds 1071)]
theorem treeEq2506 : B2506.tree = HexagonCover.NBand.M6900_7100.SplitData.node2506 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2507
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2505 : Block := .branch 151 ![385, 302231599160682369517058, 18518801667747485700, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400833085848672612346095992896] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B2506, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq2505 : B2505.tree = HexagonCover.NBand.M6900_7100.SplitData.node2505 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2506
  · rfl

def B2504 : Block := .branch 170 ![385, 302231599160682369517058, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400833085848672612346095992896] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1055).pointIds 1055), (.leaf 2 (Common.fact 1056).pointIds 1056), (.leaf 3 (Common.fact 658).pointIds 658), B2505, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 737).pointIds 737)]
theorem treeEq2504 : B2504.tree = HexagonCover.NBand.M6900_7100.SplitData.node2504 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2505
  · rfl
  · rfl

theorem accepted2504 : B2504.accepted = true := by decide +kernel
theorem checked2504 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node2504 (maskNeeds ![385, 302231599160682369517058, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400833085848672612346095992896]) := by
  rw [← treeEq2504]
  exact B2504.sound accepted2504
#print axioms checked2504

def Tip2466_2468 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2468 ![10384593717069655257060992658440577, 618970019786947162525402626, 18518801667747485700, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] checked2468
def Tip2466_2504 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2504 ![385, 302231599160682369517058, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400833085848672612346095992896] checked2504
def B2503 : Block := .branch 129 ![385, 1538, 6148, 79228162514264337593543974920, 5444517870735015415413993718908291481616, 393248, 6383839151883162018196636029936399847423433718104128] ![(.leaf 0 (Common.fact 311).pointIds 311), (.leaf 1 (Common.fact 312).pointIds 312), (.leaf 2 (Common.fact 313).pointIds 313), (.leaf 3 (Common.fact 314).pointIds 314), (.leaf 4 (Common.fact 1069).pointIds 1069), (.leaf 5 (Common.fact 315).pointIds 315), (.leaf 6 (Common.fact 1070).pointIds 1070)]
theorem treeEq2503 : B2503.tree = HexagonCover.NBand.M6900_7100.SplitData.node2503 := by
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

def B2502 : Block := .branch 132 ![385, 1538, 6148, 79228162514264337593543974920, 98320, 393248, 6383839151883162018196636029936399847423433718104128] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), B2503, (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 1068).pointIds 1068)]
theorem treeEq2502 : B2502.tree = HexagonCover.NBand.M6900_7100.SplitData.node2502 := by
  change Tree.branch (132 : Fin 173) _ = Tree.branch (132 : Fin 173) _
  apply congrArg (Tree.branch (132 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2503
  · rfl
  · rfl

def B2501 : Block := .branch 143 ![385, 1538, 6148, 79228162514264337593543974920, 1496577676626844588240573268701473812127674924105744, 393248, 6383839151883162018196636029936399847423433718104128] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), B2502, (.leaf 6 (Common.fact 1067).pointIds 1067)]
theorem treeEq2501 : B2501.tree = HexagonCover.NBand.M6900_7100.SplitData.node2501 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2502
  · rfl

def B2500 : Block := .branch 172 ![385, 144257025075840514, 18518801667747485700, 2923003274661805836486597827946830376905409060872, 1496578390250690941220513797844458536875243115479056, 393248, 397528445375783665234342955130504598912734022074432] ![(.leaf 0 (Common.fact 1009).pointIds 1009), (.leaf 1 (Common.fact 1044).pointIds 1044), (.leaf 2 (Common.fact 1045).pointIds 1045), (.leaf 3 (Common.fact 1066).pointIds 1066), (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), B2501]
theorem treeEq2500 : B2500.tree = HexagonCover.NBand.M6900_7100.SplitData.node2500 := by
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
  · exact treeEq2501

def B2499 : Block := .branch 161 ![385, 144257025075840514, 18518801667747485700, 79228162514264337593543974920, 1496578390250690941220513797844458536875243115479056, 393248, 397528445375783665234660022523066566935642560266304] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 1047).pointIds 1047), B2500, (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 1065).pointIds 1065)]
theorem treeEq2499 : B2499.tree = HexagonCover.NBand.M6900_7100.SplitData.node2499 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2500
  · rfl
  · rfl
  · rfl

def B2498 : Block := .branch 164 ![2993155353253689176481146537402947624255349848015233, 144257025075840514, 18518801667747485700, 79228162514264337593543974920, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543401065199606038621147639578688] ![(.leaf 0 (Common.fact 1064).pointIds 1064), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), B2499]
theorem treeEq2498 : B2498.tree = HexagonCover.NBand.M6900_7100.SplitData.node2498 := by
  change Tree.branch (164 : Fin 173) _ = Tree.branch (164 : Fin 173) _
  apply congrArg (Tree.branch (164 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2499

def B2497 : Block := .branch 171 ![385, 144257025075840514, 18518801667747485700, 79266848140492005727134572552, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543401065199606038621147639578688] ![B2498, (.leaf 1 (Common.fact 1051).pointIds 1051), (.leaf 2 (Common.fact 1052).pointIds 1052), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1063).pointIds 1063)]
theorem treeEq2497 : B2497.tree = HexagonCover.NBand.M6900_7100.SplitData.node2497 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2498
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2496 : Block := .branch 151 ![385, 144257025075840514, 18518801667747485700, 79266848140492005727134572552, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543401374684615859966216364359744] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B2497, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq2496 : B2496.tree = HexagonCover.NBand.M6900_7100.SplitData.node2496 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2497
  · rfl

def B2495 : Block := .branch 170 ![385, 144257025075840514, 18518801667747485700, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543401374684615859966216364359744] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1055).pointIds 1055), (.leaf 2 (Common.fact 1056).pointIds 1056), (.leaf 3 (Common.fact 658).pointIds 658), B2496, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 731).pointIds 731)]
theorem treeEq2495 : B2495.tree = HexagonCover.NBand.M6900_7100.SplitData.node2495 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2496
  · rfl
  · rfl

def B2467 : Block := .branch 89 ![10384593717069655257060992658440577, 144257025075840514, 18518801667747485700, 79344219392947341994315767816, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 104).pointIds 104), Tip2466_2468, (.leaf 2 (Common.fact 106).pointIds 106), (.leaf 3 (Common.fact 107).pointIds 107), (.leaf 4 (Common.fact 108).pointIds 108), (.leaf 5 (Common.fact 109).pointIds 109), B2495]
theorem treeEq2467 : B2467.tree = HexagonCover.NBand.M6900_7100.SplitData.node2467 := by
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
  · exact treeEq2495

def B2466 : Block := .branch 86 ![10384593717069655257060992658440577, 302231599160682369517058, 18518801667747485700, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 340).pointIds 340), (.leaf 1 (Common.fact 341).pointIds 341), (.leaf 2 (Common.fact 342).pointIds 342), B2467, (.leaf 4 (Common.fact 343).pointIds 343), (.leaf 5 (Common.fact 344).pointIds 344), Tip2466_2504]
theorem treeEq2466 : B2466.tree = HexagonCover.NBand.M6900_7100.SplitData.node2466 := by
  change Tree.branch (86 : Fin 173) _ = Tree.branch (86 : Fin 173) _
  apply congrArg (Tree.branch (86 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2467
  · rfl
  · rfl
  · rfl

theorem accepted2466 : B2466.accepted = true := by decide +kernel
theorem checked2466 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node2466 (maskNeeds ![10384593717069655257060992658440577, 302231599160682369517058, 18518801667747485700, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq2466]
  exact B2466.sound accepted2466
#print axioms checked2466

end HexagonCover.NBand.M6900_7100.SplitTree.Run0033
