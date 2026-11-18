import HexagonCover.NBand.M6900_7100.SplitData
import HexagonCover.NBand.M6900_7100.SplitTree.Run0030
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6900_7100.SplitTree.Run0031
open OwnerTree HexagonCover.NBand.M6900_7100

abbrev Block := Chunk (n := 173) (Certificate := Fin 1199) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip2351_2353 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2353 ![10387131494150190286624535863099777, 737941821641931621890, 33093458868234935605252, 116059239866245835594424328, 713623846353304459082801411451530724212047888, 393248, 21778071483256974387270895952471420043328] HexagonCover.NBand.M6900_7100.SplitTree.Run0030.checked2353
def B2374 : Block := .branch 118 ![385, 1538, 6148, 5986310706507378352962293152179508887088401699856392, 185542200051774784537577176028434367729757159440, 393248, 1496577676648622660048031884097114377512928188825664] ![(.leaf 0 (Common.fact 281).pointIds 281), (.leaf 1 (Common.fact 282).pointIds 282), (.leaf 2 (Common.fact 283).pointIds 283), (.leaf 3 (Common.fact 847).pointIds 847), (.leaf 4 (Common.fact 848).pointIds 848), (.leaf 5 (Common.fact 285).pointIds 285), (.leaf 6 (Common.fact 961).pointIds 961)]
theorem treeEq2374 : B2374.tree = HexagonCover.NBand.M6900_7100.SplitData.node2374 := by
  change Tree.branch (118 : Fin 173) _ = Tree.branch (118 : Fin 173) _
  apply congrArg (Tree.branch (118 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2373 : Block := .branch 172 ![10384596192949733827821542456689025, 147646011283225970178, 33093458868234935605252, 77373613638577702003826696, 186255823898127764478106319013159115297948532752, 393248, 1496577676648622660048031884097114377512928188825664] ![(.leaf 0 (Common.fact 943).pointIds 943), (.leaf 1 (Common.fact 944).pointIds 944), (.leaf 2 (Common.fact 945).pointIds 945), B2374, (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), (.leaf 6 (Common.fact 960).pointIds 960)]
theorem treeEq2373 : B2373.tree = HexagonCover.NBand.M6900_7100.SplitData.node2373 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2374
  · rfl
  · rfl
  · rfl

def B2372 : Block := .branch 170 ![10384596192949733827821542456689025, 147646011283225970178, 33093458868234935605252, 116059239866245835594424328, 186255823898127764478106319013159115297948532752, 393248, 21778071807458615395640565385253264818240] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 838).pointIds 838), (.leaf 2 (Common.fact 839).pointIds 839), (.leaf 3 (Common.fact 840).pointIds 840), (.leaf 4 (Common.fact 841).pointIds 841), (.leaf 5 (Common.fact 660).pointIds 660), B2373]
theorem treeEq2372 : B2372.tree = HexagonCover.NBand.M6900_7100.SplitData.node2372 := by
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
  · exact treeEq2373

def B2371 : Block := .branch 151 ![10384596192949733827821542456689025, 147646011283225970178, 33093458868234935605252, 116059239866245835594424328, 183401328512715844715989747074260125025183039504, 2993155353253689176481146537402947624255349848408096, 21778071807775528045697622735627440619584] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), B2372, (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 952).pointIds 952)]
theorem treeEq2371 : B2371.tree = HexagonCover.NBand.M6900_7100.SplitData.node2371 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2372
  · rfl
  · rfl

def B2370 : Block := .branch 132 ![10384596192949733827821542456689025, 147646011283225970178, 33093458868234935605252, 116059239866245835594424328, 183401328512715844715989747074260125025183039504, 2993155353253689176481146537402947624255349848408096, 21778071807775528045697622735627440619584] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 996).pointIds 996), (.leaf 5 (Common.fact 221).pointIds 221), B2371]
theorem treeEq2370 : B2370.tree = HexagonCover.NBand.M6900_7100.SplitData.node2370 := by
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
  · exact treeEq2371

def B2369 : Block := .branch 133 ![10384596192949733827821542456689025, 147646011283225970178, 33093458868234935605252, 116059239866245835594424328, 183401328512715844715989747074260125025183039504, 2993155353253689176481146537402947624255349848408096, 21778071807775528045697622735627440619584] ![(.leaf 0 (Common.fact 210).pointIds 210), (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), (.leaf 4 (Common.fact 995).pointIds 995), (.leaf 5 (Common.fact 215).pointIds 215), B2370]
theorem treeEq2369 : B2369.tree = HexagonCover.NBand.M6900_7100.SplitData.node2369 := by
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
  · exact treeEq2370

def B2368 : Block := .branch 157 ![10384596192949733827821542456689025, 147646011283225970178, 33093458868234935605252, 116059239866245835594424328, 713623846352979940529142984724747568191471632, 2993155353253689176481146537402947624255349848408096, 21778071807775528045697622735627440619584] ![(.leaf 0 (Common.fact 205).pointIds 205), (.leaf 1 (Common.fact 206).pointIds 206), (.leaf 2 (Common.fact 207).pointIds 207), (.leaf 3 (Common.fact 208).pointIds 208), B2369, (.leaf 5 (Common.fact 994).pointIds 994), (.leaf 0 [] 0)]
theorem treeEq2368 : B2368.tree = HexagonCover.NBand.M6900_7100.SplitData.node2368 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2369
  · rfl
  · rfl

def B2367 : Block := .branch 171 ![748288838313422304507418128500927192688373325103489, 147646011283225970178, 33093458868234935605252, 116059239866245835594424328, 713623846352979940529142984724747568191471632, 393248, 21778071807775528045697622735627440619584] ![(.leaf 0 (Common.fact 830).pointIds 830), (.leaf 1 (Common.fact 954).pointIds 954), (.leaf 2 (Common.fact 955).pointIds 955), (.leaf 3 (Common.fact 912).pointIds 912), (.leaf 4 (Common.fact 956).pointIds 956), B2368, (.leaf 6 (Common.fact 959).pointIds 959)]
theorem treeEq2367 : B2367.tree = HexagonCover.NBand.M6900_7100.SplitData.node2367 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2368
  · rfl

def B2366 : Block := .branch 169 ![10387131494150190286624535863099777, 148510702411681105410, 33111941641105664120836, 116059239866245835594424328, 713623846352979940529142984724747568191471632, 393248, 21778071807775528045697622735627440619584] ![B2367, (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 693).pointIds 693)]
theorem treeEq2366 : B2366.tree = HexagonCover.NBand.M6900_7100.SplitData.node2366 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2367
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2352 : Block := .branch 108 ![10387131494150190286624535863099777, 738806512770386757122, 33111941641105664120836, 116059239866245835594424328, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 318).pointIds 318), (.leaf 1 (Common.fact 319).pointIds 319), (.leaf 2 (Common.fact 320).pointIds 320), (.leaf 3 (Common.fact 321).pointIds 321), Tip2351_2353, (.leaf 5 (Common.fact 322).pointIds 322), B2366]
theorem treeEq2352 : B2352.tree = HexagonCover.NBand.M6900_7100.SplitData.node2352 := by
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
  · exact treeEq2366

def B2377 : Block := .branch 121 ![385, 1538, 6148, 24584, 713798070924843461022436232523752633515737104, 393248, 21778071485792275587727354755464826454080] ![(.leaf 0 (Common.fact 711).pointIds 711), (.leaf 1 (Common.fact 712).pointIds 712), (.leaf 2 (Common.fact 713).pointIds 713), (.leaf 3 (Common.fact 714).pointIds 714), (.leaf 4 (Common.fact 998).pointIds 998), (.leaf 5 (Common.fact 715).pointIds 715), (.leaf 6 (Common.fact 999).pointIds 999)]
theorem treeEq2377 : B2377.tree = HexagonCover.NBand.M6900_7100.SplitData.node2377 := by
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
  · rfl

def B2376 : Block := .branch 137 ![385, 1538, 6148, 5986310706507378352962293152179508887088401699856392, 713623846352979940529142984724747568191471632, 393248, 21778071485792275587727354755464826454080] ![(.leaf 0 (Common.fact 270).pointIds 270), (.leaf 1 (Common.fact 271).pointIds 271), (.leaf 2 (Common.fact 272).pointIds 272), (.leaf 3 (Common.fact 806).pointIds 806), B2377, (.leaf 5 (Common.fact 274).pointIds 274), (.leaf 0 [] 0)]
theorem treeEq2376 : B2376.tree = HexagonCover.NBand.M6900_7100.SplitData.node2376 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2377
  · rfl
  · rfl

def B2375 : Block := .branch 172 ![10384596192949733827821542456689025, 147646011283225970178, 33093458868234935605252, 77373613638577702003826696, 713623846352979940529142984724747568191471632, 393248, 21778071485792275587727354755464826454080] ![(.leaf 0 (Common.fact 943).pointIds 943), (.leaf 1 (Common.fact 944).pointIds 944), (.leaf 2 (Common.fact 945).pointIds 945), B2376, (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), (.leaf 6 (Common.fact 997).pointIds 997)]
theorem treeEq2375 : B2375.tree = HexagonCover.NBand.M6900_7100.SplitData.node2375 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2376
  · rfl
  · rfl
  · rfl

def B2351 : Block := .branch 101 ![10384596192949733827821542456689025, 738806512770386757122, 33111941641105664120836, 116059239866245835594424328, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![B2352, (.leaf 1 (Common.fact 460).pointIds 460), (.leaf 2 (Common.fact 461).pointIds 461), (.leaf 3 (Common.fact 462).pointIds 462), (.leaf 4 (Common.fact 463).pointIds 463), (.leaf 5 (Common.fact 464).pointIds 464), B2375]
theorem treeEq2351 : B2351.tree = HexagonCover.NBand.M6900_7100.SplitData.node2351 := by
  change Tree.branch (101 : Fin 173) _ = Tree.branch (101 : Fin 173) _
  apply congrArg (Tree.branch (101 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2352
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2375

theorem accepted2351 : B2351.accepted = true := by decide +kernel
theorem checked2351 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node2351 (maskNeeds ![10384596192949733827821542456689025, 738806512770386757122, 33111941641105664120836, 116059239866245835594424328, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328]) := by
  rw [← treeEq2351]
  exact B2351.sound accepted2351
#print axioms checked2351

def Tip2349_2351 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2351 ![10384596192949733827821542456689025, 738806512770386757122, 33111941641105664120836, 116059239866245835594424328, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] checked2351
def B2383 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 748288838335200365603543608738007802016308882047040] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 604).pointIds 604), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 704).pointIds 704)]
theorem treeEq2383 : B2383.tree = HexagonCover.NBand.M6900_7100.SplitData.node2383 := by
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

def B2382 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 748288838335200365603543608738007802016308882047040] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), B2383, (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 703).pointIds 703)]
theorem treeEq2382 : B2382.tree = HexagonCover.NBand.M6900_7100.SplitData.node2382 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2383
  · rfl
  · rfl

def B2381 : Block := .branch 169 ![2993155353253689176481149013283026195015899646263681, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 1001).pointIds 1001), (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), B2382]
theorem treeEq2381 : B2381.tree = HexagonCover.NBand.M6900_7100.SplitData.node2381 := by
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
  · exact treeEq2382

def B2380 : Block := .branch 171 ![2475880078570760549798248833, 148510702411681105410, 33111941641105664120836, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 21778071483257593357290538642608869605440] ![B2381, (.leaf 1 (Common.fact 954).pointIds 954), (.leaf 2 (Common.fact 955).pointIds 955), (.leaf 3 (Common.fact 912).pointIds 912), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1000).pointIds 1000)]
theorem treeEq2380 : B2380.tree = HexagonCover.NBand.M6900_7100.SplitData.node2380 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2381
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2379 : Block := .branch 151 ![2475880078570760549798248833, 148510702411681105410, 33111941641105664120836, 38687987410909568413229064, 1496578390250690941220513797844458536875243115479056, 393248, 21778071483257593357290538642608869605440] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B2380, (.leaf 6 (Common.fact 952).pointIds 952)]
theorem treeEq2379 : B2379.tree = HexagonCover.NBand.M6900_7100.SplitData.node2379 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2380
  · rfl

def B2378 : Block := .branch 170 ![2475880078570760549798248833, 148510702411681105410, 33111941641105664120836, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257593357290538642608869605440] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 838).pointIds 838), (.leaf 2 (Common.fact 839).pointIds 839), (.leaf 3 (Common.fact 840).pointIds 840), B2379, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 700).pointIds 700)]
theorem treeEq2378 : B2378.tree = HexagonCover.NBand.M6900_7100.SplitData.node2378 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2379
  · rfl
  · rfl

def B2350 : Block := .branch 89 ![10384596192949733827821542456689025, 738806512770386757122, 33111941641105664120836, 116059239866245835594424328, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 104).pointIds 104), Tip2349_2351, (.leaf 2 (Common.fact 106).pointIds 106), (.leaf 3 (Common.fact 107).pointIds 107), (.leaf 4 (Common.fact 108).pointIds 108), (.leaf 5 (Common.fact 109).pointIds 109), B2378]
theorem treeEq2350 : B2350.tree = HexagonCover.NBand.M6900_7100.SplitData.node2350 := by
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
  · exact treeEq2378

def B2389 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 748288838335200365603543686109260257352576063242304] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 604).pointIds 604), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 708).pointIds 708)]
theorem treeEq2389 : B2389.tree = HexagonCover.NBand.M6900_7100.SplitData.node2389 := by
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

def B2388 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 748288838335200365603543686109260257352576063242304] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), B2389, (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 707).pointIds 707)]
theorem treeEq2388 : B2388.tree = HexagonCover.NBand.M6900_7100.SplitData.node2388 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2389
  · rfl
  · rfl

def B2387 : Block := .branch 169 ![2993155353253689176481149013283026195015899646263681, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257051758523351288738601238592] ![(.leaf 0 (Common.fact 1001).pointIds 1001), (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), B2388]
theorem treeEq2387 : B2387.tree = HexagonCover.NBand.M6900_7100.SplitData.node2387 := by
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
  · exact treeEq2388

def B2386 : Block := .branch 171 ![2475880078570760549798248833, 148510702411681105410, 33111941641105664120836, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 21778071483257051758523351288738601238592] ![B2387, (.leaf 1 (Common.fact 954).pointIds 954), (.leaf 2 (Common.fact 955).pointIds 955), (.leaf 3 (Common.fact 912).pointIds 912), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1002).pointIds 1002)]
theorem treeEq2386 : B2386.tree = HexagonCover.NBand.M6900_7100.SplitData.node2386 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2387
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2385 : Block := .branch 151 ![2475880078570760549798248833, 148510702411681105410, 33111941641105664120836, 38687987410909568413229064, 1496578390250690941220513797844458536875243115479056, 393248, 21778071483257051758523351288738601238592] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B2386, (.leaf 6 (Common.fact 952).pointIds 952)]
theorem treeEq2385 : B2385.tree = HexagonCover.NBand.M6900_7100.SplitData.node2385 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2386
  · rfl

def B2384 : Block := .branch 170 ![2475880078570760549798248833, 148510702411681105410, 33111941641105664120836, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257051758523351288738601238592] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 838).pointIds 838), (.leaf 2 (Common.fact 839).pointIds 839), (.leaf 3 (Common.fact 840).pointIds 840), B2385, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 705).pointIds 705)]
theorem treeEq2384 : B2384.tree = HexagonCover.NBand.M6900_7100.SplitData.node2384 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2385
  · rfl
  · rfl

def B2349 : Block := .branch 86 ![10384596192949733827821542456689025, 738806512770386757122, 33111941641105664120836, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 340).pointIds 340), (.leaf 1 (Common.fact 341).pointIds 341), (.leaf 2 (Common.fact 342).pointIds 342), B2350, (.leaf 4 (Common.fact 343).pointIds 343), (.leaf 5 (Common.fact 344).pointIds 344), B2384]
theorem treeEq2349 : B2349.tree = HexagonCover.NBand.M6900_7100.SplitData.node2349 := by
  change Tree.branch (86 : Fin 173) _ = Tree.branch (86 : Fin 173) _
  apply congrArg (Tree.branch (86 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2350
  · rfl
  · rfl
  · exact treeEq2384

theorem accepted2349 : B2349.accepted = true := by decide +kernel
theorem checked2349 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node2349 (maskNeeds ![10384596192949733827821542456689025, 738806512770386757122, 33111941641105664120836, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328]) := by
  rw [← treeEq2349]
  exact B2349.sound accepted2349
#print axioms checked2349

def Tip2302_2315 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2315 ![10384596192950324123631901162340737, 906842010722255106999810, 33093458868234935605252, 38687987410909568413229064, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 21778072132294081704124349518783461195840] HexagonCover.NBand.M6900_7100.SplitTree.Run0030.checked2315
def B2314 : Block := .branch 142 ![385, 1538, 6148, 24584, 1427422257560190322490042680623107633475321872, 393248, 21799339780226640358090810431747946709056] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), (.leaf 4 (Common.fact 951).pointIds 951), (.leaf 5 (Common.fact 156).pointIds 156), (.leaf 6 (Common.fact 744).pointIds 744)]
theorem treeEq2314 : B2314.tree = HexagonCover.NBand.M6900_7100.SplitData.node2314 := by
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
  · rfl

def B2313 : Block := .branch 128 ![385, 1538, 6148, 5986310706507378352962293113493882659420268109258760, 1427421917277823401551579217248500201707110416, 393248, 21799339780226640358090810431747946709056] ![(.leaf 0 (Common.fact 275).pointIds 275), (.leaf 1 (Common.fact 276).pointIds 276), (.leaf 2 (Common.fact 277).pointIds 277), (.leaf 3 (Common.fact 949).pointIds 949), B2314, (.leaf 5 (Common.fact 279).pointIds 279), (.leaf 6 (Common.fact 950).pointIds 950)]
theorem treeEq2313 : B2313.tree = HexagonCover.NBand.M6900_7100.SplitData.node2313 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2314
  · rfl
  · rfl

def B2312 : Block := .branch 163 ![385, 1538, 6148, 5986310706507378352962293113493882659420268109258760, 1427421917277823401551579217248500201707110416, 393248, 21799339780226640358090810431747946709056] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), (.leaf 4 (Common.fact 854).pointIds 854), (.leaf 5 (Common.fact 262).pointIds 262), B2313]
theorem treeEq2312 : B2312.tree = HexagonCover.NBand.M6900_7100.SplitData.node2312 := by
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
  · exact treeEq2313

def B2311 : Block := .branch 137 ![385, 1538, 6148, 5986310706507378352962293113493882659420268109258760, 1427247692705959881058285969449495136382844944, 393248, 21799339780226640358090810431747946709056] ![(.leaf 0 (Common.fact 270).pointIds 270), (.leaf 1 (Common.fact 271).pointIds 271), (.leaf 2 (Common.fact 272).pointIds 272), (.leaf 3 (Common.fact 909).pointIds 909), B2312, (.leaf 5 (Common.fact 274).pointIds 274), (.leaf 0 [] 0)]
theorem treeEq2311 : B2311.tree = HexagonCover.NBand.M6900_7100.SplitData.node2311 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2312
  · rfl
  · rfl

def B2310 : Block := .branch 172 ![10384596192949733827821542456689025, 147646011283225970178, 33093458868234935605252, 38687987410909568413229064, 2140871539058939821587428954174242704574218256, 393248, 21799339780226640358090810431747946709056] ![(.leaf 0 (Common.fact 943).pointIds 943), (.leaf 1 (Common.fact 944).pointIds 944), (.leaf 2 (Common.fact 945).pointIds 945), B2311, (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), (.leaf 6 (Common.fact 948).pointIds 948)]
theorem treeEq2310 : B2310.tree = HexagonCover.NBand.M6900_7100.SplitData.node2310 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2311
  · rfl
  · rfl
  · rfl

def B2309 : Block := .branch 124 ![748288838313422304507418129105390102495687912456577, 147646011283225970178, 33093458868234935605252, 38687987410909568413229064, 2140871539058939821587428954174242704574218256, 393248, 21778072132294081704124349518783461195840] ![(.leaf 0 (Common.fact 497).pointIds 497), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B2310]
theorem treeEq2309 : B2309.tree = HexagonCover.NBand.M6900_7100.SplitData.node2309 := by
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
  · exact treeEq2310

def B2308 : Block := .branch 79 ![748288838313422304507418128501517488498732030755201, 302379100914940519646722, 33093458868234935605252, 38687987410909568413229064, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 21778072132294081704124349518783461195840] ![B2309, Tip2302_2315, (.leaf 2 (Common.fact 223).pointIds 223), (.leaf 3 (Common.fact 224).pointIds 224), (.leaf 4 (Common.fact 225).pointIds 225), (.leaf 5 (Common.fact 226).pointIds 226), (.leaf 6 (Common.fact 653).pointIds 653)]
theorem treeEq2308 : B2308.tree = HexagonCover.NBand.M6900_7100.SplitData.node2308 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2309
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2347 : Block := .branch 132 ![385, 1538, 6148, 24584, 184114952359068824656518890058984872593374412816, 393248, 21778072132294082006355804422440754872384] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 220).pointIds 220), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 977).pointIds 977)]
theorem treeEq2347 : B2347.tree = HexagonCover.NBand.M6900_7100.SplitData.node2347 := by
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

def B2346 : Block := .branch 157 ![385, 1538, 6148, 24584, 1427247692705959881058285969449495136382844944, 2993155353253731711777011654710880546081278819434528, 21778072132294082006355804422440754872384] ![(.leaf 0 (Common.fact 205).pointIds 205), (.leaf 1 (Common.fact 206).pointIds 206), (.leaf 2 (Common.fact 207).pointIds 207), (.leaf 3 (Common.fact 208).pointIds 208), B2347, (.leaf 5 (Common.fact 802).pointIds 802), (.leaf 0 [] 0)]
theorem treeEq2346 : B2346.tree = HexagonCover.NBand.M6900_7100.SplitData.node2346 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2347
  · rfl
  · rfl

def B2345 : Block := .branch 171 ![10384593717070245552871351364092289, 147646011283225970178, 33093458868234935605252, 38687987410909568413229064, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 21778072132294082006355804422440754872384] ![(.leaf 0 (Common.fact 953).pointIds 953), (.leaf 1 (Common.fact 954).pointIds 954), (.leaf 2 (Common.fact 955).pointIds 955), (.leaf 3 (Common.fact 912).pointIds 912), (.leaf 4 (Common.fact 956).pointIds 956), B2346, (.leaf 6 (Common.fact 976).pointIds 976)]
theorem treeEq2345 : B2345.tree = HexagonCover.NBand.M6900_7100.SplitData.node2345 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2346
  · rfl

def B2307 : Block := .branch 78 ![748288838313422304507418128501517488498732030755201, 147646011283225970178, 33093458868234935605252, 38687987410909568413229064, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 21778072132294081704124349518783461195840] ![(.leaf 0 (Common.fact 146).pointIds 146), B2308, (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), (.leaf 4 (Common.fact 150).pointIds 150), (.leaf 5 (Common.fact 151).pointIds 151), B2345]
theorem treeEq2307 : B2307.tree = HexagonCover.NBand.M6900_7100.SplitData.node2307 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2308
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2345

def B2306 : Block := .branch 101 ![748288838313422304504882827301061029695738624344449, 147646011283225970178, 33093458868234935605252, 38687987410909568413229064, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 21778072132294081704124349518783461195840] ![B2307, (.leaf 1 (Common.fact 460).pointIds 460), (.leaf 2 (Common.fact 461).pointIds 461), (.leaf 3 (Common.fact 462).pointIds 462), (.leaf 4 (Common.fact 463).pointIds 463), (.leaf 5 (Common.fact 464).pointIds 464), (.leaf 6 (Common.fact 652).pointIds 652)]
theorem treeEq2306 : B2306.tree = HexagonCover.NBand.M6900_7100.SplitData.node2306 := by
  change Tree.branch (101 : Fin 173) _ = Tree.branch (101 : Fin 173) _
  apply congrArg (Tree.branch (101 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2307
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2305 : Block := .branch 169 ![10384596192950324123631901162340737, 148510702411681105410, 33111941641105664120836, 38687987410909568413229064, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 21778072132294081704124349518783461195840] ![B2306, (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq2305 : B2305.tree = HexagonCover.NBand.M6900_7100.SplitData.node2305 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2306
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2304 : Block := .branch 109 ![10384596192950324123631901162340737, 148510702411681105410, 33111941641105664120836, 38687987410909568413229064, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 193).pointIds 193), (.leaf 1 (Common.fact 194).pointIds 194), (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), B2305]
theorem treeEq2304 : B2304.tree = HexagonCover.NBand.M6900_7100.SplitData.node2304 := by
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
  · exact treeEq2305

def B2303 : Block := .branch 150 ![10384596192950324123631901162340737, 148510702411681105410, 33111941641105664120836, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 42535295865117307932921825928971419680, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), B2304, (.leaf 5 (Common.fact 191).pointIds 191), (.leaf 6 (Common.fact 192).pointIds 192)]
theorem treeEq2303 : B2303.tree = HexagonCover.NBand.M6900_7100.SplitData.node2303 := by
  change Tree.branch (150 : Fin 173) _ = Tree.branch (150 : Fin 173) _
  apply congrArg (Tree.branch (150 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2304
  · rfl
  · rfl

def B2302 : Block := .branch 125 ![10384596192950324123631901162340737, 148510702411681105410, 33111941641105664120836, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 650).pointIds 650), (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), B2303, (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq2302 : B2302.tree = HexagonCover.NBand.M6900_7100.SplitData.node2302 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2303
  · rfl

theorem accepted2302 : B2302.accepted = true := by decide +kernel
theorem checked2302 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node2302 (maskNeeds ![10384596192950324123631901162340737, 148510702411681105410, 33111941641105664120836, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912]) := by
  rw [← treeEq2302]
  exact B2302.sound accepted2302
#print axioms checked2302

def Tip2298_2349 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2349 ![10384596192949733827821542456689025, 738806512770386757122, 33111941641105664120836, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] checked2349
def Tip2298_2302 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2302 ![10384596192950324123631901162340737, 148510702411681105410, 33111941641105664120836, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] checked2302
def B2395 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 2658455991569831745807614120560787472, 393248, 748288838335200365603543609040239256919966175723584] ![(.leaf 0 (Common.fact 318).pointIds 318), (.leaf 1 (Common.fact 319).pointIds 319), (.leaf 2 (Common.fact 320).pointIds 320), (.leaf 3 (Common.fact 321).pointIds 321), (.leaf 4 (Common.fact 717).pointIds 717), (.leaf 5 (Common.fact 322).pointIds 322), (.leaf 6 (Common.fact 718).pointIds 718)]
theorem treeEq2395 : B2395.tree = HexagonCover.NBand.M6900_7100.SplitData.node2395 := by
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

def B2394 : Block := .branch 121 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 748288838335200365603543609040239256919966175723584] ![(.leaf 0 (Common.fact 711).pointIds 711), (.leaf 1 (Common.fact 712).pointIds 712), (.leaf 2 (Common.fact 713).pointIds 713), (.leaf 3 (Common.fact 714).pointIds 714), B2395, (.leaf 5 (Common.fact 715).pointIds 715), (.leaf 6 (Common.fact 716).pointIds 716)]
theorem treeEq2394 : B2394.tree = HexagonCover.NBand.M6900_7100.SplitData.node2394 := by
  change Tree.branch (121 : Fin 173) _ = Tree.branch (121 : Fin 173) _
  apply congrArg (Tree.branch (121 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2395
  · rfl
  · rfl

def B2393 : Block := .branch 169 ![2993155353253689176481149013283026195015899646263681, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974689502350856128713719872] ![(.leaf 0 (Common.fact 1001).pointIds 1001), (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), B2394]
theorem treeEq2393 : B2393.tree = HexagonCover.NBand.M6900_7100.SplitData.node2393 := by
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
  · exact treeEq2394

def B2392 : Block := .branch 171 ![2475880078570760549798248833, 148510702411681105410, 33111941641105664120836, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 21778071483256974689502350856128713719872] ![B2393, (.leaf 1 (Common.fact 954).pointIds 954), (.leaf 2 (Common.fact 955).pointIds 955), (.leaf 3 (Common.fact 912).pointIds 912), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1003).pointIds 1003)]
theorem treeEq2392 : B2392.tree = HexagonCover.NBand.M6900_7100.SplitData.node2392 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2393
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2391 : Block := .branch 151 ![2475880078570760549798248833, 148510702411681105410, 33111941641105664120836, 38687987410909568413229064, 1496578390250690941220513797844458536875243115479056, 393248, 21778071483256974689502350856128713719872] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B2392, (.leaf 6 (Common.fact 952).pointIds 952)]
theorem treeEq2391 : B2391.tree = HexagonCover.NBand.M6900_7100.SplitData.node2391 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2392
  · rfl

def B2390 : Block := .branch 170 ![2475880078570760549798248833, 148510702411681105410, 33111941641105664120836, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483256974689502350856128713719872] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 838).pointIds 838), (.leaf 2 (Common.fact 839).pointIds 839), (.leaf 3 (Common.fact 840).pointIds 840), B2391, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 709).pointIds 709)]
theorem treeEq2390 : B2390.tree = HexagonCover.NBand.M6900_7100.SplitData.node2390 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2391
  · rfl
  · rfl

def B2348 : Block := .branch 78 ![10384596192949733827821542456689025, 738806512770386757122, 33111941641105664120836, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 146).pointIds 146), Tip2298_2349, (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), (.leaf 4 (Common.fact 150).pointIds 150), (.leaf 5 (Common.fact 151).pointIds 151), B2390]
theorem treeEq2348 : B2348.tree = HexagonCover.NBand.M6900_7100.SplitData.node2348 := by
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
  · exact treeEq2390

def B2301 : Block := .branch 69 ![10384596192949733827821542456689025, 148510702411681105410, 33111941641105664120836, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![Tip2298_2302, B2348, (.leaf 2 (Common.fact 491).pointIds 491), (.leaf 3 (Common.fact 492).pointIds 492), (.leaf 4 (Common.fact 493).pointIds 493), (.leaf 5 (Common.fact 494).pointIds 494), (.leaf 6 (Common.fact 649).pointIds 649)]
theorem treeEq2301 : B2301.tree = HexagonCover.NBand.M6900_7100.SplitData.node2301 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2348
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2401 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 649037107316853453566312041250832, 393248, 21778071483256974387566043857650772869184] ![(.leaf 0 (Common.fact 318).pointIds 318), (.leaf 1 (Common.fact 319).pointIds 319), (.leaf 2 (Common.fact 320).pointIds 320), (.leaf 3 (Common.fact 321).pointIds 321), (.leaf 4 (Common.fact 1007).pointIds 1007), (.leaf 5 (Common.fact 322).pointIds 322), (.leaf 6 (Common.fact 1008).pointIds 1008)]
theorem treeEq2401 : B2401.tree = HexagonCover.NBand.M6900_7100.SplitData.node2401 := by
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

def B2400 : Block := .branch 109 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 748288838335200365603543608738302949921488234872896] ![(.leaf 0 (Common.fact 193).pointIds 193), (.leaf 1 (Common.fact 194).pointIds 194), (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), B2401, (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 1006).pointIds 1006)]
theorem treeEq2400 : B2400.tree = HexagonCover.NBand.M6900_7100.SplitData.node2400 := by
  change Tree.branch (109 : Fin 173) _ = Tree.branch (109 : Fin 173) _
  apply congrArg (Tree.branch (109 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2401
  · rfl
  · rfl

def B2399 : Block := .branch 169 ![2993155353253689176481149013283026195015899646263681, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387566043857650772869184] ![(.leaf 0 (Common.fact 1001).pointIds 1001), (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), B2400]
theorem treeEq2399 : B2399.tree = HexagonCover.NBand.M6900_7100.SplitData.node2399 := by
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
  · exact treeEq2400

def B2398 : Block := .branch 171 ![2475880078570760549798248833, 148510702411681105410, 33111941641105664120836, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 21778071483256974387566043857650772869184] ![B2399, (.leaf 1 (Common.fact 954).pointIds 954), (.leaf 2 (Common.fact 955).pointIds 955), (.leaf 3 (Common.fact 912).pointIds 912), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1005).pointIds 1005)]
theorem treeEq2398 : B2398.tree = HexagonCover.NBand.M6900_7100.SplitData.node2398 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2399
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2397 : Block := .branch 151 ![2475880078570760549798248833, 148510702411681105410, 33111941641105664120836, 38687987410909568413229064, 1496578390250690941220513797844458536875243115479056, 393248, 21778071483256974387566043857650772869184] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B2398, (.leaf 6 (Common.fact 952).pointIds 952)]
theorem treeEq2397 : B2397.tree = HexagonCover.NBand.M6900_7100.SplitData.node2397 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2398
  · rfl

def B2396 : Block := .branch 170 ![2475880078570760549798248833, 148510702411681105410, 33111941641105664120836, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387566043857650772869184] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 838).pointIds 838), (.leaf 2 (Common.fact 839).pointIds 839), (.leaf 3 (Common.fact 840).pointIds 840), B2397, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 1004).pointIds 1004)]
theorem treeEq2396 : B2396.tree = HexagonCover.NBand.M6900_7100.SplitData.node2396 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2397
  · rfl
  · rfl

def B2300 : Block := .branch 68 ![10384596192949733827821542456689025, 148510702411681105410, 33111941641105664120836, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 445).pointIds 445), B2301, (.leaf 2 (Common.fact 446).pointIds 446), (.leaf 3 (Common.fact 447).pointIds 447), (.leaf 4 (Common.fact 448).pointIds 448), (.leaf 5 (Common.fact 449).pointIds 449), B2396]
theorem treeEq2300 : B2300.tree = HexagonCover.NBand.M6900_7100.SplitData.node2300 := by
  change Tree.branch (68 : Fin 173) _ = Tree.branch (68 : Fin 173) _
  apply congrArg (Tree.branch (68 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2301
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2396

def B2299 : Block := .branch 91 ![10384593717069655257060992658440577, 148510702411681105410, 33111941641105664120836, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![B2300, (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), (.leaf 3 (Common.fact 333).pointIds 333), (.leaf 4 (Common.fact 334).pointIds 334), (.leaf 5 (Common.fact 335).pointIds 335), (.leaf 6 (Common.fact 648).pointIds 648)]
theorem treeEq2299 : B2299.tree = HexagonCover.NBand.M6900_7100.SplitData.node2299 := by
  change Tree.branch (91 : Fin 173) _ = Tree.branch (91 : Fin 173) _
  apply congrArg (Tree.branch (91 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2300
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2298 : Block := .branch 113 ![385, 148510702411681105410, 33111941641105664120836, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![B2299, (.leaf 1 (Common.fact 253).pointIds 253), (.leaf 2 (Common.fact 254).pointIds 254), (.leaf 3 (Common.fact 255).pointIds 255), (.leaf 4 (Common.fact 256).pointIds 256), (.leaf 5 (Common.fact 257).pointIds 257), (.leaf 6 (Common.fact 942).pointIds 942)]
theorem treeEq2298 : B2298.tree = HexagonCover.NBand.M6900_7100.SplitData.node2298 := by
  change Tree.branch (113 : Fin 173) _ = Tree.branch (113 : Fin 173) _
  apply congrArg (Tree.branch (113 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2299
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted2298 : B2298.accepted = true := by decide +kernel
theorem checked2298 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node2298 (maskNeeds ![385, 148510702411681105410, 33111941641105664120836, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912]) := by
  rw [← treeEq2298]
  exact B2298.sound accepted2298
#print axioms checked2298

def Tip2134_2137 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2137 ![1208925819614629174706561, 302379965606068974781954, 89780339435541406685188, 79266850501675247161957179400, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] HexagonCover.NBand.M6900_7100.SplitTree.Run0030.checked2137
def Tip2134_2298 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2298 ![385, 148510702411681105410, 33111941641105664120836, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] checked2298
def B2290 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 604).pointIds 604), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 936).pointIds 936)]
theorem treeEq2290 : B2290.tree = HexagonCover.NBand.M6900_7100.SplitData.node2290 := by
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

def B2289 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), B2290, (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 935).pointIds 935)]
theorem treeEq2289 : B2289.tree = HexagonCover.NBand.M6900_7100.SplitData.node2289 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2290
  · rfl
  · rfl

def B2288 : Block := .branch 166 ![385, 1538, 6148, 24584, 98320, 2854495385411919762116571938898990272765886496, 21778071483257130263143762513720633720896] ![B2289, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 934).pointIds 934)]
theorem treeEq2288 : B2288.tree = HexagonCover.NBand.M6900_7100.SplitData.node2288 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2289
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2287 : Block := .branch 151 ![385, 1538, 6148, 24584, 1496577676626844588240573268701473812127674924105744, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B2288, (.leaf 6 (Common.fact 933).pointIds 933)]
theorem treeEq2287 : B2287.tree = HexagonCover.NBand.M6900_7100.SplitData.node2287 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2288
  · rfl

def B2286 : Block := .branch 170 ![385, 147646011283225970178, 36893488147419109380, 38687987410909568413229064, 98320, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 838).pointIds 838), (.leaf 2 (Common.fact 839).pointIds 839), (.leaf 3 (Common.fact 840).pointIds 840), B2287, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 932).pointIds 932)]
theorem treeEq2286 : B2286.tree = HexagonCover.NBand.M6900_7100.SplitData.node2286 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2287
  · rfl
  · rfl

def B2136 : Block := .branch 80 ![385, 302379965606068974781954, 89780339435541406685188, 79266850501675247161957179400, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![Tip2134_2137, (.leaf 1 (Common.fact 764).pointIds 764), (.leaf 2 (Common.fact 765).pointIds 765), (.leaf 3 (Common.fact 766).pointIds 766), (.leaf 4 (Common.fact 767).pointIds 767), (.leaf 5 (Common.fact 768).pointIds 768), B2286]
theorem treeEq2136 : B2136.tree = HexagonCover.NBand.M6900_7100.SplitData.node2136 := by
  change Tree.branch (80 : Fin 173) _ = Tree.branch (80 : Fin 173) _
  apply congrArg (Tree.branch (80 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2286

def B2297 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 604).pointIds 604), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 941).pointIds 941)]
theorem treeEq2297 : B2297.tree = HexagonCover.NBand.M6900_7100.SplitData.node2297 := by
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

def B2296 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 748288838335200365603543763707186303866586214694976] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), B2297, (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 940).pointIds 940)]
theorem treeEq2296 : B2296.tree = HexagonCover.NBand.M6900_7100.SplitData.node2296 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2297
  · rfl
  · rfl

def B2295 : Block := .branch 169 ![42535295865117307932921825928971026817, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 853).pointIds 853), (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), B2296]
theorem treeEq2295 : B2295.tree = HexagonCover.NBand.M6900_7100.SplitData.node2295 := by
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
  · exact treeEq2296

def B2294 : Block := .branch 125 ![385, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2865645758011185073687339798035314453518876704, 21778071483257438841459219147817477472320] ![B2295, (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), (.leaf 5 (Common.fact 482).pointIds 482), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq2294 : B2294.tree = HexagonCover.NBand.M6900_7100.SplitData.node2294 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2295
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2293 : Block := .branch 143 ![385, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 21778071483257438841459219147817477472320] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), B2294, (.leaf 6 (Common.fact 939).pointIds 939)]
theorem treeEq2293 : B2293.tree = HexagonCover.NBand.M6900_7100.SplitData.node2293 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2294
  · rfl

def B2292 : Block := .branch 151 ![385, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 21778071483257438841459219147817477472320] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B2293, (.leaf 6 (Common.fact 938).pointIds 938)]
theorem treeEq2292 : B2292.tree = HexagonCover.NBand.M6900_7100.SplitData.node2292 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2293
  · rfl

def B2291 : Block := .branch 170 ![385, 148510702411681105410, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438841459219147817477472320] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 838).pointIds 838), (.leaf 2 (Common.fact 839).pointIds 839), (.leaf 3 (Common.fact 840).pointIds 840), B2292, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 937).pointIds 937)]
theorem treeEq2291 : B2291.tree = HexagonCover.NBand.M6900_7100.SplitData.node2291 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2292
  · rfl
  · rfl

def B2135 : Block := .branch 78 ![385, 148510702411681105410, 89780339435541406685188, 79266850501675247161957179400, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 146).pointIds 146), B2136, (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), (.leaf 4 (Common.fact 150).pointIds 150), (.leaf 5 (Common.fact 151).pointIds 151), B2291]
theorem treeEq2135 : B2135.tree = HexagonCover.NBand.M6900_7100.SplitData.node2135 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2136
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2291

def B2134 : Block := .branch 76 ![385, 148510702411681105410, 33111941641105664120836, 79266850501675247161957179400, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 413).pointIds 413), (.leaf 1 (Common.fact 414).pointIds 414), B2135, (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), Tip2134_2298]
theorem treeEq2134 : B2134.tree = HexagonCover.NBand.M6900_7100.SplitData.node2134 := by
  change Tree.branch (76 : Fin 173) _ = Tree.branch (76 : Fin 173) _
  apply congrArg (Tree.branch (76 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2135
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted2134 : B2134.accepted = true := by decide +kernel
theorem checked2134 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node2134 (maskNeeds ![385, 148510702411681105410, 33111941641105664120836, 79266850501675247161957179400, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq2134]
  exact B2134.sound accepted2134
#print axioms checked2134

end HexagonCover.NBand.M6900_7100.SplitTree.Run0031
