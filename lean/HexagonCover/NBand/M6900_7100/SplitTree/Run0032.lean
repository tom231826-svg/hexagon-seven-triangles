import HexagonCover.NBand.M6900_7100.SplitData
import HexagonCover.NBand.M6900_7100.SplitTree.Run0000
import HexagonCover.NBand.M6900_7100.SplitTree.Run0027
import HexagonCover.NBand.M6900_7100.SplitTree.Run0028
import HexagonCover.NBand.M6900_7100.SplitTree.Run0031
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6900_7100.SplitTree.Run0032
open OwnerTree HexagonCover.NBand.M6900_7100

abbrev Block := Chunk (n := 173) (Certificate := Fin 1199) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip2132_2134 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2134 ![385, 148510702411681105410, 33111941641105664120836, 79266850501675247161957179400, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] HexagonCover.NBand.M6900_7100.SplitTree.Run0031.checked2134
def B2410 : Block := .branch 169 ![2993155353253689176481146537402947624255349848015233, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 5998002719627803647790863079356796219561733164367936] ![(.leaf 0 (Common.fact 928).pointIds 928), (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 1018).pointIds 1018)]
theorem treeEq2410 : B2410.tree = HexagonCover.NBand.M6900_7100.SplitData.node2410 := by
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

def B2409 : Block := .branch 171 ![385, 148510702411681105410, 14222475709627083266052, 38706876876841046994083848, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 5998002719627803647790863079356796219561733164367936] ![B2410, (.leaf 1 (Common.fact 954).pointIds 954), (.leaf 2 (Common.fact 1015).pointIds 1015), (.leaf 3 (Common.fact 1016).pointIds 1016), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1017).pointIds 1017)]
theorem treeEq2409 : B2409.tree = HexagonCover.NBand.M6900_7100.SplitData.node2409 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2410
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2408 : Block := .branch 163 ![385, 148510702411681105410, 14222475709627083266052, 38706876876841046994083848, 1496578395825877240853169583228388105037333491974160, 2854495385411919762116571938898990272765886496, 5986310706529156424445233600695065955404485704024128] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), (.leaf 4 (Common.fact 734).pointIds 734), (.leaf 5 (Common.fact 262).pointIds 262), B2409]
theorem treeEq2408 : B2408.tree = HexagonCover.NBand.M6900_7100.SplitData.node2408 := by
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
  · exact treeEq2409

def B2407 : Block := .branch 165 ![385, 148510702411681105410, 14222475709627083266052, 38706876876841046994083848, 1496578395825877240853169583228388105037333491974160, 2854495385411919762116571938898990272765886496, 5986310706529156424445233600695065955404485704024128] ![(.leaf 0 (Common.fact 355).pointIds 355), (.leaf 1 (Common.fact 356).pointIds 356), (.leaf 2 (Common.fact 357).pointIds 357), (.leaf 3 (Common.fact 358).pointIds 358), (.leaf 4 (Common.fact 733).pointIds 733), B2408, (.leaf 0 [] 0)]
theorem treeEq2407 : B2407.tree = HexagonCover.NBand.M6900_7100.SplitData.node2407 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2408
  · rfl

def B2406 : Block := .branch 167 ![385, 148510702411681105410, 14222475709627083266052, 38706876876841046994083848, 1496578395825877240853169583228388105037333491974160, 2854495385411919762116571938898990272765886496, 5986310706529156424445233600695065955404485704024128] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 732).pointIds 732), B2407, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq2406 : B2406.tree = HexagonCover.NBand.M6900_7100.SplitData.node2406 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2407
  · rfl

def B2405 : Block := .branch 142 ![385, 148510702411681105410, 14222475709627083266052, 38706876876841046994083848, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 5986310706529156424445233600695065955404485704024128] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), B2406, (.leaf 5 (Common.fact 156).pointIds 156), (.leaf 6 (Common.fact 1014).pointIds 1014)]
theorem treeEq2405 : B2405.tree = HexagonCover.NBand.M6900_7100.SplitData.node2405 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2406
  · rfl
  · rfl

def B2404 : Block := .branch 151 ![385, 148510702411681105410, 14222475709627083266052, 38706876876841046994083848, 1496578390250690941220513797844458536875243115479056, 393248, 5986310706529156424445233600695065955404485704024128] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B2405, (.leaf 6 (Common.fact 1013).pointIds 1013)]
theorem treeEq2404 : B2404.tree = HexagonCover.NBand.M6900_7100.SplitData.node2404 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2405
  · rfl

def B2403 : Block := .branch 170 ![385, 148510702411681105410, 14222475709627083266052, 38706876876841046994083848, 713623846352979940529142984724747568191471632, 393248, 5986310706529156424445233600695065955404485704024128] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 838).pointIds 838), (.leaf 2 (Common.fact 839).pointIds 839), (.leaf 3 (Common.fact 840).pointIds 840), B2404, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 1012).pointIds 1012)]
theorem treeEq2403 : B2403.tree = HexagonCover.NBand.M6900_7100.SplitData.node2403 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2404
  · rfl
  · rfl

def B2402 : Block := .branch 172 ![385, 148510702411681105410, 14222475709627083266052, 38706876876841046994083848, 713623846352979940529142984724747568191471632, 393248, 21778071482940525889170706893786007994432] ![(.leaf 0 (Common.fact 1009).pointIds 1009), (.leaf 1 (Common.fact 944).pointIds 944), (.leaf 2 (Common.fact 1010).pointIds 1010), (.leaf 3 (Common.fact 1011).pointIds 1011), (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), B2403]
theorem treeEq2402 : B2402.tree = HexagonCover.NBand.M6900_7100.SplitData.node2402 := by
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
  · exact treeEq2403

def B2133 : Block := .branch 74 ![385, 148510702411681105410, 14222475709627083266052, 79266850501675247161957179400, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 455).pointIds 455), (.leaf 1 (Common.fact 456).pointIds 456), Tip2132_2134, B2402, (.leaf 4 (Common.fact 457).pointIds 457), (.leaf 5 (Common.fact 458).pointIds 458), (.leaf 6 (Common.fact 459).pointIds 459)]
theorem treeEq2133 : B2133.tree = HexagonCover.NBand.M6900_7100.SplitData.node2133 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2402
  · rfl
  · rfl
  · rfl

def B2419 : Block := .branch 169 ![2993155353253689176481146537402947624255349848015233, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 5998002719627803647790863079356796219561733164367936] ![(.leaf 0 (Common.fact 928).pointIds 928), (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 1018).pointIds 1018)]
theorem treeEq2419 : B2419.tree = HexagonCover.NBand.M6900_7100.SplitData.node2419 := by
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

def B2418 : Block := .branch 171 ![385, 148510702411681105410, 4777742743887792838660, 38697432143875307703656456, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 5998002719627803647790863079356796219561733164367936] ![B2419, (.leaf 1 (Common.fact 954).pointIds 954), (.leaf 2 (Common.fact 1021).pointIds 1021), (.leaf 3 (Common.fact 1022).pointIds 1022), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1017).pointIds 1017)]
theorem treeEq2418 : B2418.tree = HexagonCover.NBand.M6900_7100.SplitData.node2418 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2419
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2417 : Block := .branch 163 ![385, 148510702411681105410, 4777742743887792838660, 38697432143875307703656456, 1496578395825877240853169583228388105037333491974160, 2854495385411919762116571938898990272765886496, 5986310706529156424445233600695065955404485704024128] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), (.leaf 4 (Common.fact 734).pointIds 734), (.leaf 5 (Common.fact 262).pointIds 262), B2418]
theorem treeEq2417 : B2417.tree = HexagonCover.NBand.M6900_7100.SplitData.node2417 := by
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
  · exact treeEq2418

def B2416 : Block := .branch 165 ![385, 148510702411681105410, 4777742743887792838660, 38697432143875307703656456, 1496578395825877240853169583228388105037333491974160, 2854495385411919762116571938898990272765886496, 5986310706529156424445233600695065955404485704024128] ![(.leaf 0 (Common.fact 355).pointIds 355), (.leaf 1 (Common.fact 356).pointIds 356), (.leaf 2 (Common.fact 357).pointIds 357), (.leaf 3 (Common.fact 358).pointIds 358), (.leaf 4 (Common.fact 733).pointIds 733), B2417, (.leaf 0 [] 0)]
theorem treeEq2416 : B2416.tree = HexagonCover.NBand.M6900_7100.SplitData.node2416 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2417
  · rfl

def B2415 : Block := .branch 167 ![385, 148510702411681105410, 4777742743887792838660, 38697432143875307703656456, 1496578395825877240853169583228388105037333491974160, 2854495385411919762116571938898990272765886496, 5986310706529156424445233600695065955404485704024128] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 732).pointIds 732), B2416, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq2415 : B2415.tree = HexagonCover.NBand.M6900_7100.SplitData.node2415 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2416
  · rfl

def B2414 : Block := .branch 142 ![385, 148510702411681105410, 4777742743887792838660, 38697432143875307703656456, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 5986310706529156424445233600695065955404485704024128] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), B2415, (.leaf 5 (Common.fact 156).pointIds 156), (.leaf 6 (Common.fact 1014).pointIds 1014)]
theorem treeEq2414 : B2414.tree = HexagonCover.NBand.M6900_7100.SplitData.node2414 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2415
  · rfl
  · rfl

def B2413 : Block := .branch 151 ![385, 148510702411681105410, 4777742743887792838660, 38697432143875307703656456, 1496578390250690941220513797844458536875243115479056, 393248, 5986310706529156424445233600695065955404485704024128] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B2414, (.leaf 6 (Common.fact 1013).pointIds 1013)]
theorem treeEq2413 : B2413.tree = HexagonCover.NBand.M6900_7100.SplitData.node2413 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2414
  · rfl

def B2412 : Block := .branch 170 ![385, 148510702411681105410, 4777742743887792838660, 38697432143875307703656456, 713623846352979940529142984724747568191471632, 393248, 5986310706529156424445233600695065955404485704024128] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 838).pointIds 838), (.leaf 2 (Common.fact 839).pointIds 839), (.leaf 3 (Common.fact 840).pointIds 840), B2413, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 1012).pointIds 1012)]
theorem treeEq2412 : B2412.tree = HexagonCover.NBand.M6900_7100.SplitData.node2412 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2413
  · rfl
  · rfl

def B2411 : Block := .branch 172 ![385, 148510702411681105410, 4777742743887792838660, 38697432143875307703656456, 713623846352979940529142984724747568191471632, 393248, 21778071482940525889170706893786007994432] ![(.leaf 0 (Common.fact 1009).pointIds 1009), (.leaf 1 (Common.fact 944).pointIds 944), (.leaf 2 (Common.fact 1019).pointIds 1019), (.leaf 3 (Common.fact 1020).pointIds 1020), (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), B2412]
theorem treeEq2411 : B2411.tree = HexagonCover.NBand.M6900_7100.SplitData.node2411 := by
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
  · exact treeEq2412

def B2132 : Block := .branch 73 ![385, 148510702411681105410, 4777742743887792838660, 79266850501675247161957179400, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 450).pointIds 450), (.leaf 1 (Common.fact 451).pointIds 451), B2133, B2411, (.leaf 4 (Common.fact 452).pointIds 452), (.leaf 5 (Common.fact 453).pointIds 453), (.leaf 6 (Common.fact 454).pointIds 454)]
theorem treeEq2132 : B2132.tree = HexagonCover.NBand.M6900_7100.SplitData.node2132 := by
  change Tree.branch (73 : Fin 173) _ = Tree.branch (73 : Fin 173) _
  apply congrArg (Tree.branch (73 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2133
  · exact treeEq2411
  · rfl
  · rfl
  · rfl

theorem accepted2132 : B2132.accepted = true := by decide +kernel
theorem checked2132 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node2132 (maskNeeds ![385, 148510702411681105410, 4777742743887792838660, 79266850501675247161957179400, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq2132]
  exact B2132.sound accepted2132
#print axioms checked2132

def Tip0118_2052 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2052 ![10384596192949733827821542456689025, 1033954417949739582978, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] HexagonCover.NBand.M6900_7100.SplitTree.Run0027.checked2052
def Tip0118_2000 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2000 ![10384593717070245552871351364092289, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] HexagonCover.NBand.M6900_7100.SplitTree.Run0027.checked2000
def Tip0118_1883 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node1883 ![10384593717069655257060992658440577, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] HexagonCover.NBand.M6900_7100.SplitTree.Run0027.checked1883
def Tip0118_1635 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node1635 ![10384593717069655257060992658440577, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] HexagonCover.NBand.M6900_7100.SplitTree.Run0028.checked1635
def Tip0118_1139 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node1139 ![10384593717069655257060992658440577, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] HexagonCover.NBand.M6900_7100.SplitTree.Run0028.checked1139
def Tip0118_0122 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node0122 ![10384593717069655257060992658440577, 443658607591033931266, 7138925985322615445508, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] HexagonCover.NBand.M6900_7100.SplitTree.Run0028.checked0122
def B2128 : Block := .branch 109 ![385, 1538, 6148, 24584, 5846006549323611672814739330865132078623730270224, 393248, 748288838335200365603543609040239256919966175723584] ![(.leaf 0 (Common.fact 193).pointIds 193), (.leaf 1 (Common.fact 194).pointIds 194), (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 752).pointIds 752), (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 753).pointIds 753)]
theorem treeEq2128 : B2128.tree = HexagonCover.NBand.M6900_7100.SplitData.node2128 := by
  change Tree.branch (109 : Fin 173) _ = Tree.branch (109 : Fin 173) _
  apply congrArg (Tree.branch (109 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2127 : Block := .branch 162 ![385, 1538, 6148, 38690348594151003235835912, 98320, 393248, 748288838335200365603543609040239256919966175723584] ![(.leaf 0 (Common.fact 350).pointIds 350), (.leaf 1 (Common.fact 351).pointIds 351), (.leaf 2 (Common.fact 352).pointIds 352), (.leaf 3 (Common.fact 758).pointIds 758), B2128, (.leaf 5 (Common.fact 353).pointIds 353), (.leaf 6 (Common.fact 751).pointIds 751)]
theorem treeEq2127 : B2127.tree = HexagonCover.NBand.M6900_7100.SplitData.node2127 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2128
  · rfl
  · rfl

def B2126 : Block := .branch 169 ![93536104789220322060903422481853605844458452025729, 936749822004692482, 18482772870728521732, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483256974689502350856128713719872] ![(.leaf 0 (Common.fact 702).pointIds 702), (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), B2127]
theorem treeEq2126 : B2126.tree = HexagonCover.NBand.M6900_7100.SplitData.node2126 := by
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
  · exact treeEq2127

def B2125 : Block := .branch 125 ![93536104789177786765038305173920684018529480999297, 936749822004692482, 18482772870728521732, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 2865645758011185073687339798035314453518876704, 21778071483257438917017082873731800891456] ![B2126, (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), (.leaf 5 (Common.fact 482).pointIds 482), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq2125 : B2125.tree = HexagonCover.NBand.M6900_7100.SplitData.node2125 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2126
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2124 : Block := .branch 143 ![93536104789177786765038305173920684018529480999297, 936749822004692482, 18482772870728521732, 38690348594151003235835912, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 21778071483257438917017082873731800891456] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), B2125, (.leaf 6 (Common.fact 710).pointIds 710)]
theorem treeEq2124 : B2124.tree = HexagonCover.NBand.M6900_7100.SplitData.node2124 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2125
  · rfl

def B2123 : Block := .branch 166 ![2475880078570760549798248833, 936749822004692482, 18482772870728521732, 38690348594151003235835912, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543400756092385535905650531893312] ![B2124, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq2123 : B2123.tree = HexagonCover.NBand.M6900_7100.SplitData.node2123 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2124
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2122 : Block := .branch 151 ![2475880078570760549798248833, 936749822004692482, 18482772870728521732, 38690348594151003235835912, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400756092385535905650531893312] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B2123, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq2122 : B2122.tree = HexagonCover.NBand.M6900_7100.SplitData.node2122 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2123
  · rfl

def B2121 : Block := .branch 170 ![10384596192949733827821542456689025, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400756092385535905650531893312] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 760).pointIds 760), (.leaf 3 (Common.fact 761).pointIds 761), B2122, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 709).pointIds 709)]
theorem treeEq2121 : B2121.tree = HexagonCover.NBand.M6900_7100.SplitData.node2121 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2122
  · rfl
  · rfl

def B2051 : Block := .branch 78 ![10384596192949733827821542456689025, 1033954417949739582978, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 146).pointIds 146), Tip0118_2052, (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), (.leaf 4 (Common.fact 150).pointIds 150), (.leaf 5 (Common.fact 151).pointIds 151), B2121]
theorem treeEq2051 : B2051.tree = HexagonCover.NBand.M6900_7100.SplitData.node2051 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2121

def B1999 : Block := .branch 69 ![10384596192949733827821542456689025, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![Tip0118_2000, B2051, (.leaf 2 (Common.fact 491).pointIds 491), (.leaf 3 (Common.fact 492).pointIds 492), (.leaf 4 (Common.fact 493).pointIds 493), (.leaf 5 (Common.fact 494).pointIds 494), (.leaf 6 (Common.fact 649).pointIds 649)]
theorem treeEq1999 : B1999.tree = HexagonCover.NBand.M6900_7100.SplitData.node1999 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2051
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1998 : Block := .branch 91 ![10384593717069655257060992658440577, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![B1999, (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), (.leaf 3 (Common.fact 333).pointIds 333), (.leaf 4 (Common.fact 334).pointIds 334), (.leaf 5 (Common.fact 335).pointIds 335), (.leaf 6 (Common.fact 648).pointIds 648)]
theorem treeEq1998 : B1998.tree = HexagonCover.NBand.M6900_7100.SplitData.node1998 := by
  change Tree.branch (91 : Fin 173) _ = Tree.branch (91 : Fin 173) _
  apply congrArg (Tree.branch (91 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1999
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1882 : Block := .branch 76 ![10384593717069655257060992658440577, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 413).pointIds 413), (.leaf 1 (Common.fact 414).pointIds 414), Tip0118_1883, (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), B1998]
theorem treeEq1882 : B1882.tree = HexagonCover.NBand.M6900_7100.SplitData.node1882 := by
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
  · exact treeEq1998

def B1634 : Block := .branch 74 ![10384593717069655257060992658440577, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 455).pointIds 455), (.leaf 1 (Common.fact 456).pointIds 456), Tip0118_1635, B1882, (.leaf 4 (Common.fact 457).pointIds 457), (.leaf 5 (Common.fact 458).pointIds 458), (.leaf 6 (Common.fact 459).pointIds 459)]
theorem treeEq1634 : B1634.tree = HexagonCover.NBand.M6900_7100.SplitData.node1634 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1882
  · rfl
  · rfl
  · rfl

def B1138 : Block := .branch 73 ![10384593717069655257060992658440577, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 450).pointIds 450), (.leaf 1 (Common.fact 451).pointIds 451), Tip0118_1139, B1634, (.leaf 4 (Common.fact 452).pointIds 452), (.leaf 5 (Common.fact 453).pointIds 453), (.leaf 6 (Common.fact 454).pointIds 454)]
theorem treeEq1138 : B1138.tree = HexagonCover.NBand.M6900_7100.SplitData.node1138 := by
  change Tree.branch (73 : Fin 173) _ = Tree.branch (73 : Fin 173) _
  apply congrArg (Tree.branch (73 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1634
  · rfl
  · rfl
  · rfl

def B0121 : Block := .branch 72 ![10384593717069655257060992658440577, 443658607591033931266, 2416559502452970231812, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 421).pointIds 421), (.leaf 1 (Common.fact 422).pointIds 422), Tip0118_0122, B1138, (.leaf 4 (Common.fact 423).pointIds 423), (.leaf 5 (Common.fact 424).pointIds 424), (.leaf 6 (Common.fact 425).pointIds 425)]
theorem treeEq0121 : B0121.tree = HexagonCover.NBand.M6900_7100.SplitData.node0121 := by
  change Tree.branch (72 : Fin 173) _ = Tree.branch (72 : Fin 173) _
  apply congrArg (Tree.branch (72 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1138
  · rfl
  · rfl
  · rfl

def B2130 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 374144419178489218543400446229881543836189542842432] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 604).pointIds 604), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 763).pointIds 763)]
theorem treeEq2130 : B2130.tree = HexagonCover.NBand.M6900_7100.SplitData.node2130 := by
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

def B2129 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 374144419178489218543400446229881543836189542842432] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), B2130, (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 762).pointIds 762)]
theorem treeEq2129 : B2129.tree = HexagonCover.NBand.M6900_7100.SplitData.node2129 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2130
  · rfl
  · rfl

def B0120 : Block := .branch 68 ![10384593717069655257060992658440577, 148510702411681105410, 2416559502452970231812, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 445).pointIds 445), B0121, (.leaf 2 (Common.fact 446).pointIds 446), (.leaf 3 (Common.fact 447).pointIds 447), (.leaf 4 (Common.fact 448).pointIds 448), (.leaf 5 (Common.fact 449).pointIds 449), B2129]
theorem treeEq0120 : B0120.tree = HexagonCover.NBand.M6900_7100.SplitData.node0120 := by
  change Tree.branch (68 : Fin 173) _ = Tree.branch (68 : Fin 173) _
  apply congrArg (Tree.branch (68 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0121
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2129

def B0119 : Block := .branch 113 ![385, 148510702411681105410, 2416559502452970231812, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![B0120, (.leaf 1 (Common.fact 253).pointIds 253), (.leaf 2 (Common.fact 254).pointIds 254), (.leaf 3 (Common.fact 255).pointIds 255), (.leaf 4 (Common.fact 256).pointIds 256), (.leaf 5 (Common.fact 257).pointIds 257), (.leaf 6 (Common.fact 444).pointIds 444)]
theorem treeEq0119 : B0119.tree = HexagonCover.NBand.M6900_7100.SplitData.node0119 := by
  change Tree.branch (113 : Fin 173) _ = Tree.branch (113 : Fin 173) _
  apply congrArg (Tree.branch (113 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0120
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0118 : Block := .branch 168 ![385, 148510702411681105410, 2416559502452970231812, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 391).pointIds 391), (.leaf 1 (Common.fact 392).pointIds 392), (.leaf 2 (Common.fact 406).pointIds 406), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), B0119]
theorem treeEq0118 : B0118.tree = HexagonCover.NBand.M6900_7100.SplitData.node0118 := by
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
  · exact treeEq0119

theorem accepted0118 : B0118.accepted = true := by decide +kernel
theorem checked0118 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node0118 (maskNeeds ![385, 148510702411681105410, 2416559502452970231812, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0118]
  exact B0118.sound accepted0118
#print axioms checked0118

def B2453 : Block := .branch 79 ![748288838313443561768219193004703366976801947517313, 730750818665451459101842416358141510927477900802, 6148, 24584, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 486).pointIds 486), (.leaf 1 (Common.fact 487).pointIds 487), (.leaf 2 (Common.fact 223).pointIds 223), (.leaf 3 (Common.fact 224).pointIds 224), (.leaf 4 (Common.fact 225).pointIds 225), (.leaf 5 (Common.fact 226).pointIds 226), (.leaf 6 (Common.fact 1041).pointIds 1041)]
theorem treeEq2453 : B2453.tree = HexagonCover.NBand.M6900_7100.SplitData.node2453 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2452 : Block := .branch 159 ![748288838313443561768219193004703366976801947517313, 1099511629314, 6148, 24584, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 484).pointIds 484), B2453, (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 232).pointIds 232), (.leaf 5 (Common.fact 233).pointIds 233), (.leaf 6 (Common.fact 1040).pointIds 1040)]
theorem treeEq2452 : B2452.tree = HexagonCover.NBand.M6900_7100.SplitData.node2452 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2453
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2451 : Block := .branch 124 ![748288838313422294120286634350736906063837462004097, 1099511629314, 6148, 24584, 98320, 393248, 21778071483256974311749925714704515727424] ![B2452, (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), (.leaf 6 (Common.fact 1039).pointIds 1039)]
theorem treeEq2451 : B2451.tree = HexagonCover.NBand.M6900_7100.SplitData.node2451 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2452
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2450 : Block := .branch 138 ![748288838313422294120286634350736906063837462004097, 1099511629314, 6148, 79228162514264337593543974920, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 134).pointIds 134), (.leaf 1 (Common.fact 135).pointIds 135), (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), B2451, (.leaf 5 (Common.fact 138).pointIds 138), (.leaf 6 (Common.fact 1038).pointIds 1038)]
theorem treeEq2450 : B2450.tree = HexagonCover.NBand.M6900_7100.SplitData.node2450 := by
  change Tree.branch (138 : Fin 173) _ = Tree.branch (138 : Fin 173) _
  apply congrArg (Tree.branch (138 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2451
  · rfl
  · rfl

def B2449 : Block := .branch 139 ![748288838313422294120286634350736906063837462004097, 1099511629314, 6148, 79228162514264337593543974920, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 128).pointIds 128), (.leaf 1 (Common.fact 129).pointIds 129), (.leaf 2 (Common.fact 130).pointIds 130), (.leaf 3 (Common.fact 131).pointIds 131), B2450, (.leaf 5 (Common.fact 132).pointIds 132), (.leaf 6 (Common.fact 1037).pointIds 1037)]
theorem treeEq2449 : B2449.tree = HexagonCover.NBand.M6900_7100.SplitData.node2449 := by
  change Tree.branch (139 : Fin 173) _ = Tree.branch (139 : Fin 173) _
  apply congrArg (Tree.branch (139 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2450
  · rfl
  · rfl

def B2448 : Block := .branch 140 ![748288838313422294120286634350736906063837462004097, 1099511629314, 6148, 79228162514264337593543974920, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 122).pointIds 122), (.leaf 1 (Common.fact 123).pointIds 123), (.leaf 2 (Common.fact 124).pointIds 124), (.leaf 3 (Common.fact 125).pointIds 125), B2449, (.leaf 5 (Common.fact 126).pointIds 126), (.leaf 6 (Common.fact 1036).pointIds 1036)]
theorem treeEq2448 : B2448.tree = HexagonCover.NBand.M6900_7100.SplitData.node2448 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2449
  · rfl
  · rfl

def B2447 : Block := .branch 141 ![748288838313422294120286634350736906063837462004097, 1099511629314, 6148, 79228162514264337593543974920, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 116).pointIds 116), (.leaf 1 (Common.fact 117).pointIds 117), (.leaf 2 (Common.fact 118).pointIds 118), (.leaf 3 (Common.fact 119).pointIds 119), B2448, (.leaf 5 (Common.fact 120).pointIds 120), (.leaf 6 (Common.fact 1035).pointIds 1035)]
theorem treeEq2447 : B2447.tree = HexagonCover.NBand.M6900_7100.SplitData.node2447 := by
  change Tree.branch (141 : Fin 173) _ = Tree.branch (141 : Fin 173) _
  apply congrArg (Tree.branch (141 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2448
  · rfl
  · rfl

def B2446 : Block := .branch 142 ![748288838313422294120286634350736906063837462004097, 1099511629314, 6148, 79228162514264337593543974920, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), B2447, (.leaf 5 (Common.fact 156).pointIds 156), (.leaf 6 (Common.fact 1034).pointIds 1034)]
theorem treeEq2446 : B2446.tree = HexagonCover.NBand.M6900_7100.SplitData.node2446 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2447
  · rfl
  · rfl

def B2445 : Block := .branch 68 ![748288838313422294120286634350736906063837462004097, 1099511629314, 6148, 79228162514264337593543974920, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 1032).pointIds 1032), B2446, (.leaf 2 (Common.fact 446).pointIds 446), (.leaf 3 (Common.fact 447).pointIds 447), (.leaf 4 (Common.fact 448).pointIds 448), (.leaf 5 (Common.fact 449).pointIds 449), (.leaf 6 (Common.fact 1033).pointIds 1033)]
theorem treeEq2445 : B2445.tree = HexagonCover.NBand.M6900_7100.SplitData.node2445 := by
  change Tree.branch (68 : Fin 173) _ = Tree.branch (68 : Fin 173) _
  apply congrArg (Tree.branch (68 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2446
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2444 : Block := .branch 129 ![748288838313422294120286634350736906063837462004097, 1099511629314, 6148, 79228162514264337593543974920, 11150372599265311570767859136324180753088528, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 311).pointIds 311), (.leaf 1 (Common.fact 312).pointIds 312), (.leaf 2 (Common.fact 313).pointIds 313), (.leaf 3 (Common.fact 314).pointIds 314), (.leaf 4 (Common.fact 524).pointIds 524), (.leaf 5 (Common.fact 315).pointIds 315), B2445]
theorem treeEq2444 : B2444.tree = HexagonCover.NBand.M6900_7100.SplitData.node2444 := by
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
  · exact treeEq2445

def B2443 : Block := .branch 130 ![748288838313422294120286634350736906063837462004097, 1099511629314, 6148, 79228162514264337593543974920, 11150372599265311570767859136324180753088528, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 518).pointIds 518), (.leaf 1 (Common.fact 519).pointIds 519), (.leaf 2 (Common.fact 520).pointIds 520), (.leaf 3 (Common.fact 521).pointIds 521), (.leaf 4 (Common.fact 522).pointIds 522), (.leaf 5 (Common.fact 523).pointIds 523), B2444]
theorem treeEq2443 : B2443.tree = HexagonCover.NBand.M6900_7100.SplitData.node2443 := by
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
  · exact treeEq2444

def B2442 : Block := .branch 131 ![748288838313422294120286634350736906063837462004097, 1099511629314, 6148, 79228162514264337593543974920, 11150372599265311570767859136324180753088528, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 512).pointIds 512), (.leaf 1 (Common.fact 513).pointIds 513), (.leaf 2 (Common.fact 514).pointIds 514), (.leaf 3 (Common.fact 515).pointIds 515), (.leaf 4 (Common.fact 516).pointIds 516), (.leaf 5 (Common.fact 517).pointIds 517), B2443]
theorem treeEq2442 : B2442.tree = HexagonCover.NBand.M6900_7100.SplitData.node2442 := by
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
  · exact treeEq2443

def B2441 : Block := .branch 132 ![748288838313422294120286634350736906063837462004097, 1099511629314, 6148, 79228162514264337593543974920, 11150372599265311570767859136324180753088528, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 511).pointIds 511), (.leaf 5 (Common.fact 221).pointIds 221), B2442]
theorem treeEq2441 : B2441.tree = HexagonCover.NBand.M6900_7100.SplitData.node2441 := by
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
  · exact treeEq2442

def B2440 : Block := .branch 133 ![748288838313422294120286634350736906063837462004097, 1099511629314, 6148, 79228162514264337593543974920, 11150372599265311570767859136324180753088528, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 210).pointIds 210), (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), (.leaf 4 (Common.fact 510).pointIds 510), (.leaf 5 (Common.fact 215).pointIds 215), B2441]
theorem treeEq2440 : B2440.tree = HexagonCover.NBand.M6900_7100.SplitData.node2440 := by
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
  · exact treeEq2441

def B2439 : Block := .branch 163 ![748288838313422294120286634350736906063837462004097, 1099511629314, 6148, 79228162514264337593543974920, 11150372599265311570767859136324180753088528, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), (.leaf 4 (Common.fact 507).pointIds 507), (.leaf 5 (Common.fact 262).pointIds 262), B2440]
theorem treeEq2439 : B2439.tree = HexagonCover.NBand.M6900_7100.SplitData.node2439 := by
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
  · exact treeEq2440

def B2438 : Block := .branch 165 ![748288838313422294120286634350736906063837462004097, 1099511629314, 6148, 79228162514264337593543974920, 11150372599265311570767859136324180753088528, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 355).pointIds 355), (.leaf 1 (Common.fact 356).pointIds 356), (.leaf 2 (Common.fact 357).pointIds 357), (.leaf 3 (Common.fact 358).pointIds 358), (.leaf 4 (Common.fact 506).pointIds 506), B2439, (.leaf 0 [] 0)]
theorem treeEq2438 : B2438.tree = HexagonCover.NBand.M6900_7100.SplitData.node2438 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2439
  · rfl

def B2437 : Block := .branch 167 ![748288838313422294120286634350736906063837462004097, 1099511629314, 6148, 79228162514264337593543974920, 11150372599265311570767859136324180753088528, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 504).pointIds 504), B2438, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq2437 : B2437.tree = HexagonCover.NBand.M6900_7100.SplitData.node2437 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2438
  · rfl

def B2436 : Block := .branch 143 ![748288838313422294120286634350736906063837462004097, 1099511629314, 6148, 79228162514264337593543974920, 98320, 42535295865117307932921825928971419680, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), B2437, (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 1031).pointIds 1031)]
theorem treeEq2436 : B2436.tree = HexagonCover.NBand.M6900_7100.SplitData.node2436 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2437
  · rfl
  · rfl

def B2435 : Block := .branch 109 ![748288838313422294120286634350736906063837462004097, 1099511629314, 6148, 79228162514264337593543974920, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 193).pointIds 193), (.leaf 1 (Common.fact 194).pointIds 194), (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), B2436]
theorem treeEq2435 : B2435.tree = HexagonCover.NBand.M6900_7100.SplitData.node2435 := by
  change Tree.branch (109 : Fin 173) _ = Tree.branch (109 : Fin 173) _
  apply congrArg (Tree.branch (109 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2436

def B2434 : Block := .branch 150 ![748288838313422294120286634350736906063837462004097, 1099511629314, 6148, 79228162514264337593543974920, 98320, 42535295865117307932921825928971419680, 21778071483257438539264657732307602899008] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), B2435, (.leaf 5 (Common.fact 191).pointIds 191), (.leaf 6 (Common.fact 192).pointIds 192)]
theorem treeEq2434 : B2434.tree = HexagonCover.NBand.M6900_7100.SplitData.node2434 := by
  change Tree.branch (150 : Fin 173) _ = Tree.branch (150 : Fin 173) _
  apply congrArg (Tree.branch (150 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2435
  · rfl
  · rfl

theorem accepted2434 : B2434.accepted = true := by decide +kernel
theorem checked2434 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node2434 (maskNeeds ![748288838313422294120286634350736906063837462004097, 1099511629314, 6148, 79228162514264337593543974920, 98320, 42535295865117307932921825928971419680, 21778071483257438539264657732307602899008]) := by
  rw [← treeEq2434]
  exact B2434.sound accepted2434
#print axioms checked2434

def Tip0077_0095 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node0095 ![604463486268066890776961, 1461501637330902918203685134947737924412737848834, 374144419156711147060143317175405346520066150111236, 38685626227668133590622216, 182687704666362864775460604089535377456991666192, 93536104789177786765035829293842113257979683143712, 27243867386518729678263475937025619132480] HexagonCover.NBand.M6900_7100.SplitTree.Run0000.checked0095
def B0094 : Block := .branch 79 ![576460752303423873, 1461501637330902918203685134947737924412737848834, 374144419156711147060143317175405346520066150111236, 38685626227668133590622216, 182687704666362864775460604089535377456991666192, 93536104789177786765035829293842113257979683143712, 27243867386518729678263475937025619132480] ![Tip0077_0095, (.leaf 1 (Common.fact 404).pointIds 404), (.leaf 2 (Common.fact 223).pointIds 223), (.leaf 3 (Common.fact 224).pointIds 224), (.leaf 4 (Common.fact 225).pointIds 225), (.leaf 5 (Common.fact 226).pointIds 226), (.leaf 6 (Common.fact 227).pointIds 227)]
theorem treeEq0094 : B0094.tree = HexagonCover.NBand.M6900_7100.SplitData.node0094 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0093 : Block := .branch 90 ![576460752303423873, 1461501637330902918203685134947737924412737848834, 374144419156711147060143317175405346520066150111236, 38685626227668133590622216, 182687704666362864775460604089535377456991666192, 93536104789177786765035829293842113257979683143712, 27243867386518729678263475937025619132480] ![(.leaf 0 (Common.fact 398).pointIds 398), (.leaf 1 (Common.fact 399).pointIds 399), (.leaf 2 (Common.fact 400).pointIds 400), (.leaf 3 (Common.fact 401).pointIds 401), (.leaf 4 (Common.fact 402).pointIds 402), (.leaf 5 (Common.fact 403).pointIds 403), B0094]
theorem treeEq0093 : B0093.tree = HexagonCover.NBand.M6900_7100.SplitData.node0093 := by
  change Tree.branch (90 : Fin 173) _ = Tree.branch (90 : Fin 173) _
  apply congrArg (Tree.branch (90 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0094

def B0092 : Block := .branch 160 ![576460752303423873, 302231454904756805305858, 374144419156711147060143317175405346520066150111236, 38685626227668133590622216, 182687704666362864775460604089535377456991666192, 93536104789177786765035829293842113257979683143712, 27243867386518729678263475937025619132480] ![(.leaf 0 (Common.fact 299).pointIds 299), B0093, (.leaf 2 (Common.fact 397).pointIds 397), (.leaf 3 (Common.fact 301).pointIds 301), (.leaf 4 (Common.fact 302).pointIds 302), (.leaf 5 (Common.fact 303).pointIds 303), (.leaf 6 (Common.fact 304).pointIds 304)]
theorem treeEq0092 : B0092.tree = HexagonCover.NBand.M6900_7100.SplitData.node0092 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0093
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0091 : Block := .branch 168 ![576460752303423873, 302231815192726994945538, 36893488147419109380, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 93536104789177786765035829293842113257979683143712, 27243867386518729678263475937025619132480] ![(.leaf 0 (Common.fact 391).pointIds 391), (.leaf 1 (Common.fact 392).pointIds 392), B0092, (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 396).pointIds 396)]
theorem treeEq0091 : B0091.tree = HexagonCover.NBand.M6900_7100.SplitData.node0091 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0092
  · rfl
  · rfl
  · rfl
  · rfl

def B0090 : Block := .branch 113 ![576460752303423873, 302231815192726994945538, 36893488147419109380, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 93536104789177786765035829293842113257979683143712, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 390).pointIds 390), (.leaf 1 (Common.fact 253).pointIds 253), (.leaf 2 (Common.fact 254).pointIds 254), (.leaf 3 (Common.fact 255).pointIds 255), (.leaf 4 (Common.fact 256).pointIds 256), (.leaf 5 (Common.fact 257).pointIds 257), B0091]
theorem treeEq0090 : B0090.tree = HexagonCover.NBand.M6900_7100.SplitData.node0090 := by
  change Tree.branch (113 : Fin 173) _ = Tree.branch (113 : Fin 173) _
  apply congrArg (Tree.branch (113 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0091

def B0089 : Block := .branch 65 ![576460752303423873, 302231815192726994945538, 6148, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 93536104789177786765035829293842113257979683143712, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), B0090, (.leaf 3 (Common.fact 142).pointIds 142), (.leaf 4 (Common.fact 143).pointIds 143), (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 389).pointIds 389)]
theorem treeEq0089 : B0089.tree = HexagonCover.NBand.M6900_7100.SplitData.node0089 := by
  change Tree.branch (65 : Fin 173) _ = Tree.branch (65 : Fin 173) _
  apply congrArg (Tree.branch (65 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0090
  · rfl
  · rfl
  · rfl
  · rfl

def B0088 : Block := .branch 138 ![576460752303423873, 302231815192726994945538, 6148, 79266848140492005727134572552, 183401328512715844715989747074260125025183039504, 93536104789177786765035829293842113257979683143712, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 134).pointIds 134), (.leaf 1 (Common.fact 135).pointIds 135), (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), B0089, (.leaf 5 (Common.fact 138).pointIds 138), (.leaf 6 (Common.fact 388).pointIds 388)]
theorem treeEq0088 : B0088.tree = HexagonCover.NBand.M6900_7100.SplitData.node0088 := by
  change Tree.branch (138 : Fin 173) _ = Tree.branch (138 : Fin 173) _
  apply congrArg (Tree.branch (138 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0089
  · rfl
  · rfl

def B0087 : Block := .branch 141 ![576460752303423873, 302231815192726994945538, 6148, 79266848140492005727134572552, 183401328512715844715989747074260125025183039504, 93536104789177786765035829293842113257979683143712, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 116).pointIds 116), (.leaf 1 (Common.fact 117).pointIds 117), (.leaf 2 (Common.fact 118).pointIds 118), (.leaf 3 (Common.fact 119).pointIds 119), B0088, (.leaf 5 (Common.fact 120).pointIds 120), (.leaf 6 (Common.fact 387).pointIds 387)]
theorem treeEq0087 : B0087.tree = HexagonCover.NBand.M6900_7100.SplitData.node0087 := by
  change Tree.branch (141 : Fin 173) _ = Tree.branch (141 : Fin 173) _
  apply congrArg (Tree.branch (141 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0088
  · rfl
  · rfl

def B0086 : Block := .branch 124 ![576460752303423873, 302231815192726994945538, 6148, 79266848140492005727134572552, 183401328512715844715989747074260125025183039504, 93536104789177786765035829293842113257979683143712, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 386).pointIds 386), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B0087]
theorem treeEq0086 : B0086.tree = HexagonCover.NBand.M6900_7100.SplitData.node0086 := by
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
  · exact treeEq0087

def B0085 : Block := .branch 78 ![576460752303423873, 360289069701268994, 6148, 79266848140492005727134572552, 183401328512715844715989747074260125025183039504, 93536104789177786765035829293842113257979683143712, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 146).pointIds 146), B0086, (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), (.leaf 4 (Common.fact 150).pointIds 150), (.leaf 5 (Common.fact 151).pointIds 151), (.leaf 6 (Common.fact 239).pointIds 239)]
theorem treeEq0085 : B0085.tree = HexagonCover.NBand.M6900_7100.SplitData.node0085 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0086
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0084 : Block := .branch 132 ![576460752303423873, 360289069701268994, 6148, 79266848140492005727134572552, 184828576205421804597048033043709620161565786128, 93536104789177786765035829293842113257979683143712, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 220).pointIds 220), (.leaf 5 (Common.fact 221).pointIds 221), B0085]
theorem treeEq0084 : B0084.tree = HexagonCover.NBand.M6900_7100.SplitData.node0084 := by
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
  · exact treeEq0085

def B0083 : Block := .branch 133 ![576460752303423873, 360289069701268994, 6148, 79266848140492005727134572552, 184828576205421804597048033043709620161565786128, 93536104789177786765035829293842113257979683143712, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 210).pointIds 210), (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), (.leaf 4 (Common.fact 214).pointIds 214), (.leaf 5 (Common.fact 215).pointIds 215), B0084]
theorem treeEq0083 : B0083.tree = HexagonCover.NBand.M6900_7100.SplitData.node0083 := by
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
  · exact treeEq0084

def B0082 : Block := .branch 157 ![576460752303423873, 360289069701268994, 6148, 79266848140492005727134572552, 2140871539058939821587428954174242704574218256, 93536104789177786765035829293842113257979683143712, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 205).pointIds 205), (.leaf 1 (Common.fact 206).pointIds 206), (.leaf 2 (Common.fact 207).pointIds 207), (.leaf 3 (Common.fact 208).pointIds 208), B0083, (.leaf 5 (Common.fact 209).pointIds 209), (.leaf 0 [] 0)]
theorem treeEq0082 : B0082.tree = HexagonCover.NBand.M6900_7100.SplitData.node0082 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0083
  · rfl
  · rfl

def B0081 : Block := .branch 166 ![576460752303423873, 360289069701268994, 6148, 79266848140492005727134572552, 2140871539058939821587428954174242704574218256, 393248, 21778072132294545856081217810472224948288] ![(.leaf 0 (Common.fact 385).pointIds 385), (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), B0082, (.leaf 6 (Common.fact 204).pointIds 204)]
theorem treeEq0081 : B0081.tree = HexagonCover.NBand.M6900_7100.SplitData.node0081 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0082
  · rfl

def B0080 : Block := .branch 109 ![576460752303423873, 360289069701268994, 6148, 79266848140492005727134572552, 2140871539058939821587428954174242704574218256, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 193).pointIds 193), (.leaf 1 (Common.fact 194).pointIds 194), (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), B0081]
theorem treeEq0080 : B0080.tree = HexagonCover.NBand.M6900_7100.SplitData.node0080 := by
  change Tree.branch (109 : Fin 173) _ = Tree.branch (109 : Fin 173) _
  apply congrArg (Tree.branch (109 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0081

def B0079 : Block := .branch 150 ![576460752303423873, 360289069701268994, 6148, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), B0080, (.leaf 5 (Common.fact 191).pointIds 191), (.leaf 6 (Common.fact 192).pointIds 192)]
theorem treeEq0079 : B0079.tree = HexagonCover.NBand.M6900_7100.SplitData.node0079 := by
  change Tree.branch (150 : Fin 173) _ = Tree.branch (150 : Fin 173) _
  apply congrArg (Tree.branch (150 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0080
  · rfl
  · rfl

def B0078 : Block := .branch 125 ![576460752303423873, 360289069701268994, 6148, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 384).pointIds 384), (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), B0079, (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq0078 : B0078.tree = HexagonCover.NBand.M6900_7100.SplitData.node0078 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0079
  · rfl

def B0077 : Block := .branch 164 ![576460752303423873, 360289069701268994, 6148, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), B0078]
theorem treeEq0077 : B0077.tree = HexagonCover.NBand.M6900_7100.SplitData.node0077 := by
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
  · exact treeEq0078

theorem accepted0077 : B0077.accepted = true := by decide +kernel
theorem checked0077 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node0077 (maskNeeds ![576460752303423873, 360289069701268994, 6148, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0077]
  exact B0077.sound accepted0077
#print axioms checked0077

end HexagonCover.NBand.M6900_7100.SplitTree.Run0032
